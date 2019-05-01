//==============================================================================
// mcs_player.js
//==============================================================================
//------------------------------------------------------------------------------
// Start-up:
//   cd <this folder>
//   node player.js <optional port>
//
// Requires only standard nodejs modules and epilog.js (in this folder)
//------------------------------------------------------------------------------

var http = require("http");
var url = require("url");
var querystring = require("querystring");
var fs = require('fs');
eval(fs.readFileSync('epilog.js') + '');

//==============================================================================
// Player
//==============================================================================
//------------------------------------------------------------------------------
// Player subroutines call GGP basic subroutines (defined below)
// Legal play by default; modify these subroutines to implement other players
//------------------------------------------------------------------------------
var matchid = '';
var role = '';
var library = seq();
var startclock = 0;
var playclock = 0;

var roles = seq();
var state = null;
var limit = 1;
const padtime = 2500;

//------------------------------------------------------------------------------

function info ()
 {return 'ready'}

function start (id,r,rs,sc,pc)
 {matchid = id;
  library = definemorerules(seq(),rs);
  role = r;
  roles = findroles(library);
  state = findinits(library);
  startclock = sc;
  playclock = pc;
  return 'ready'}

function play (id,move){
    const starttime = Date.now();
    if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
    return bestmove(role, state, library, starttime);

    /*
    if (roles.length > 1) {
	return bestmovemulti(role, state, library, starttime);
    }
    else{
	return bestmovesingle(role, state, library);
    }
    */
}


function randomelement(arr) {
    var item = arr[Math.floor(Math.random()*arr.length)];
    return item;
}


// best move
function bestmove(role, state, library, starttime){

    // find all legal moves
    var actions = findlegals(role, state, library);

    actions.sort(() => Math.random() - 0.5);

    var action = actions[0];
    var score = 0;

    if (actions.length == 1)
	return action[2];

    // iterate through all legal moves
    for (var i = 0; i < actions.length; i++) {

	// timeout protection
	const elapsed = Date.now() - starttime;
	if (elapsed >= ((playclock * 1000) - padtime)) {
	    return action[2];
	}

	// max score if only player
	if (roles.length == 1){
	    var result = parseInt(maxscore(role, state, library, level, starttime));
	}
	// find minimax score if we make current move, more than 1 player
	else{
	    var result = parseInt(minscore(role, actions[i], state, library, 0, starttime, 0, seq())); 
	}
	
	// maybe reinstate, max montecarlo at 99?
    	// bound at max score
    	if (result == 100){
    	    return actions[i][2];
    	}
	
    	// keep the best action
    	if (parseInt(result) > parseInt(score)){
    	    score = result;
    	    action = actions[i];
    	}
    }

    return action[2];
}


// max score
function maxscore(role, state, library, level, starttime){
    
    // determine if end state
    if (findterminalp(state, library)){
	return parseInt(findreward(role, state, library));
    }

    // timeout protection
    const elapsed = Date.now() - starttime;
    if (elapsed >= ((playclock * 1000) - padtime)) {
	return 0;
    }

    // find legal actions 
    var actions = findlegals(role, state, library);
    var score = 0;

    // monte carlo
    if (level >= limit) {
	//return montecarlo(role,state,4,library);
	var mcs_score = parseInt(montecarlo(role,state,4,library, starttime));
	console.log(mcs_score);
	// if 100 subtract 1?  if 0 add 1? avoid definite loss, avoid missing definite win
	return parseInt(mcs_score);
    }

    // iterate through actions
    for (var i = 0; i < actions.length; i++){
	if (roles.length == 1){
	    var result = parseInt(maxscore(role, state, library, level, starttime));
	}
	else{
	    var result = parseInt(minscore(role, actions[i], state, library, level)); 
	}

	// make distinction for non monte carlo?
	// bound at max score
	if (result == 100) {
	    return 100;
	}

	// keep best score
	if (result > score){
	    score = result;
	}
    }

    return score;
}


// needs to be called once for each minimizing player
function minscore(role, action, state, library, level, starttime, opponent_idx, move){
    
    // if opponent counter is outside indices of roles, we have a complete move sequence
    
    // if current role is player, we are starting
    if (roles[opponent_idx] == role){

	move[opponent_idx] = action;

	// call minscore for next role
	return minscore(role, action, state, library, level, starttime, opponent_idx+1, move);
    }

    // if current role is an opponent, iterate through all moves
    else if (opponent_idx < roles.length){

	var opponent = roles[opponentIdx];
	var actions = findlegals(opponent, state, library);

	var score = 100;

	for (var i = 0; i < actions.length; i++){
	    move[opponent_idx] = actions[i];

	    // call minscore for next role
	    var result = minscore(role, action, state, library, level, starttime, opponent_idx+1, move);

	    // bound at min score
	    if (result == 0){
		return 0;
	    }
	
	    // keep lowest score
	    if (result < score){
		score = result;
	    }
	}

	return score;
    }
    
    // we have a complete move (action for all roles), now can minimize
    else{
	
	var newstate = simulate(move, state, library);

	// now maximizing players picks next move
	var result = parseInt(maxscore(role, newstate, library, level+1, starttime));

	return result;
    }
}


function montecarlo(role, state, count, library, starttime){
  var total = 0;
  for (var i = 0; i < count; i++) {
      newnum = depthcharge(role, state, library, starttime);
      total = total + newnum;
  }
  return total / count;
}


function depthcharge (role, state, library, starttime) {
  
    if (findterminalp(state,library)) {
      //console.log("reward")
      //console.log(findreward(role,state,library))
      return parseInt(findreward(role,state,library))
    };

    const elapsed = Date.now() - starttime;
    if (elapsed >= ((playclock * 1000) - padtime)) {
	return 0;
    }

    var move = seq();
    for (var i=0; i<roles.length; i++) {
      var options = findlegals(roles[i],state,library);
      move[i] = randomelement(options)
    };
    var newstate = simulate(move,state, library);
    return depthcharge(role,newstate, library);
    


    /* iterative version
    var newstate = state;

    while (!findterminalp(newstate,library)){

	const elapsed = Date.now() - starttime;
	if (elapsed >= ((playclock * 1000) - padtime)) {
	    return 0;
	}

	var move = seq();
	for (var i=0; i<roles.length; i++) {
	    var options = findlegals(roles[i],newstate,library);
	    move[i] = randomelement(options);
	}
	newstate = simulate(move, newstate, library);
    }
    return parseInt(findreward(role,newstate,library));
    */
 }







/*
function bestmovemulti(role, state, library, starttime){
    // find all legal moves
    var actions = findlegals(role, state, library);

    actions.sort(() => Math.random() - 0.5);

    var action = actions[0];
    var score = 0;

    if (actions.length == 1)
	return action[2];

    console.log("number of moves " + actions.length);

    // iterate through all legal moves
    for (var i = 0; i < actions.length; i++) {

	const elapsed = Date.now() - starttime;
	if (elapsed >= ((playclock * 1000) - padtime)) {
	    return action[2];
	}

    	// find minimax score if we make current move
    	var result = minscore(role, actions[i], state, library, 1, starttime); 

	
    	// bound at max score
    	//if (result == 100){
    	//    return 100;
    	//}
	
	
    	// keep the best action
    	if (parseInt(result) > parseInt(score)){
    	    score = result;
    	    action = actions[i];
    	}

      if (parseInt(result) == parseInt(score) && Math.random() < 0.3){
          score = result;
          action = actions[i];
      }
    }

    return action[2];
}
*/


/*
function bestmovesingle(role, state, library) {
  var actions = findlegals(role, state, library);
  var action = actions[0];
  var score = 0;
  for (var i=0; i<actions.length; i++)
      {
        var result = maxscoresingle(role, simulate([actions[i]], state, library), library, 1);
       if (result==100) {return actions[i][2]};
       if (parseInt(result) > parseInt(score)) {
        score = result; action = actions[i]
      }
    };
  return action[2]
}
*/

/*
function maxscoremulti(role, state, library, level, starttime){
    // determine if end state
    if (findterminalp(state, library)){
	return findreward(role, state, library);
    }

    // timeout protection
    const elapsed = Date.now() - starttime;
    if (elapsed >= ((playclock * 1000) - padtime)) {
	return 0;
    }

    // find legal actions 
    var actions = findlegals(role, state, library);
    var score = 0;

    if (level >= limit) {
	//return montecarlo(role,state,4,library);
	var montescore = montecarlo(role,state,4,library, starttime);
	console.log(montescore);
	return montescore;
    }

    // iterate through actions
    for (var i = 0; i < actions.length; i++){
      var result = minscore(role, actions[i], state, library, level); 
      // bound at max score
      if (result == 100) {
          return 100;
      }
      // keep best score
      if (result > score){
          score = result;
      }
    }

    return score;
}
 */

/*
function maxscoresingle(role, state, library, level)
{
  //console.log("On level " + level + " and state" + state)
  if (findterminalp(state, library))
     {return findreward(role, state, library)};

  if (level >= limit) {return montecarlo(role,state,4,library)};
  var actions = findlegals(role, state, library);
  var score = 0;
  for (var i=0; i<actions.length; i++) {
       var result = parseInt(maxscoresingle(role, simulate([actions[i]], state, library), library, level + 1));
       //console.log("Action is " + actions[i] + " and result is " + result)
       //console.log("score is " + score)
       if (result>score) {
          score = result
       }
  };
  return score
}
*/

 /*
// returns opponent's role; assumes a 2-player game (fine as we only evaluate on tic tac toe)
function findopponent(role, library){
    roles = findroles(library)

    if (role == roles[0]){
	return roles[1];
    }
    else{
	return roles[0];
    }
}
 */



  
function abort (id)
  {return 'done'}

function stop (id,move)
  {return 'done'}

//==============================================================================
// GGP basics
//==============================================================================

indexing = true;
dataindexing = false;
ruleindexing = true;

function findroles (rules)
 {return basefinds('R',seq('role','R'),seq(),rules)}

function findbases (rules)
 {return basefinds('P',seq('base','P'),seq(),rules)}

function findinputs (role,rules)
 {return basefinds('A',seq('input',role,'A'),seq(),rules)}

function findinits (rules)
 {return basefinds(seq('true','P'),seq('init','P'),seq(),rules)}

function findlegalp (role,ply,facts,rules)
 {return basefindp(seq('legal',role,ply),facts,rules)}

function findlegalx (role,facts,rules)
 {return basefindx(seq('does',role,'X'),seq('legal',role,'X'),facts,rules)}

function findlegals (role,facts,rules)
 {return basefinds(seq('does',role,'X'),seq('legal',role,'X'),facts,rules)}

function findnexts (facts,rules)
 {return basefinds(seq('true','P'),seq('next','P'),facts,rules).sort()}

function findterminalp (facts,rules)
 {return basefindp('terminal',facts,rules)}

function findreward (role,facts,rules)
 {return basefindx('R',seq('goal',role,'R'),facts,rules)}

function simulate (move,state,rules)
 {if (move==='nil') {return state};
  return findnexts(move.concat(state),rules)}

//------------------------------------------------------------------------------

function doesify (roles,actions)
 {var exp = seq();
  for (var i=0; i<roles.length; i++)
      {exp[i] = seq('does',roles[i],actions[i])};
  return exp}

function undoesify (move)
 {var exp = seq();
  for (var i=0; i<move.length; i++)
      {exp[i] = move[i][2]};
  return exp}

function truify (state)
 {var exp = seq();
  for (var i=0; i<state.length; i++)
      {exp[i] = seq('true',state[i])};
  return exp}

function untruify (state)
 {var exp = seq();
  for (var i=0; i<state.length; i++)
      {exp[i] = state[i][1]};
  return exp}

//==============================================================================
// Logic programming subroutines
//==============================================================================
//------------------------------------------------------------------------------
// basefindp, basefindx, basefinds are defined in epilog.js
//------------------------------------------------------------------------------
//==============================================================================
// Web Server
//==============================================================================
//------------------------------------------------------------------------------
// Listens for connections and calls player functions (defined above)
//------------------------------------------------------------------------------

function onRequest(request,response)
 {if (request.method === 'OPTIONS')
     {var headers = {};
      headers["Access-Control-Allow-Origin"] = "*";
      headers["Access-Control-Allow-Methods"] = "POST, GET, OPTIONS";
      headers["Access-Control-Allow-Credentials"] = false;
      headers["Access-Control-Max-Age"] = '86400';
      headers["Access-Control-Allow-Headers"] = "Sender, Receiver, Content-Type, Accept";
      response.writeHead(200, headers);
      response.end()}
  else{
response.writeHead(200,
   {"Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Methods": "POST, GET, OPTIONS",
    "Access-Control-Allow-Headers": "*",
    "Access-Control-Allow-Age": "86400",
    "Content-Type": "text/plain"});
  var postData = "";
  var pathname = url.parse(request.url).pathname;
  request.setEncoding("utf8");
  request.addListener("data",function (chunk) {postData += chunk});
  request.addListener("end",function () {route(pathname,response,postData)})}}

function route (pathname,response,postData)
 {var request = readkif(postData);
  console.log(printseq(request));
  var result = eval(request[0]).apply(null,request.slice(1));
  response.write(printit(result));
  console.log(printit(result));
  response.end()}

//------------------------------------------------------------------------------

var port = (process.argv.length>2) ? process.argv[2] : 9147;
http.createServer(onRequest).listen(port);
console.log("Server has started.");

//==============================================================================
// End
//==============================================================================
