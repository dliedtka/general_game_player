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
var limit = 2;
const padtime = 2500;
var depthchargelimit = 8;

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

function play (id,move)
 {if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
  var start = Date.now();
  depthchargelimit = 8;
  if (roles.length > 1) {
    return iterative_depthcharge(role, state, library, start, bestmovemulti);
  } else {
    return bestmovesingle(role, state, library);
  }}

function iterative_depthcharge(role, state, library, start, bestmove) {
  var actions = findlegals(role, state, library);
  var action = actions[0];
  var score = 0;

  if (actions.length == 1) {
    return action[2];
  }

  while(true) {
    depthchargelimit += 1;
    console.log(depthchargelimit);
    [curraction, currscore] = bestmove(role, state, library, start);
    // console.log('current action: ' + action + ': ' + score + ', new action: ' + curraction[2] + ': ' + currscore);
    const elapsed = Date.now() - start;
    if (elapsed >= ((playclock * 1000) - padtime)) {
      console.log('Found move: ' + action[2] + ', ' + score);
      return action[2];
    }
    if (parseInt(currscore) >= parseInt(score)) {
      score = parseInt(currscore);
      action = curraction;
    }
  }
}

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

function montecarlo (role,state,count, library, start){
  console.log("calling montecarlo")
  var total = 0;
  for (var i=0; i<count; i++) {
    newnum = depthcharge(role,state, library, start, 1)
    total = total + newnum
  };
  return total/count;
}

// from https://stackoverflow.com/questions/2450954/how-to-randomize-shuffle-a-javascript-array
function shuffle(array) {
  var currentIndex = array.length, temporaryValue, randomIndex;

  // While there remain elements to shuffle...
  while (0 !== currentIndex) {

    // Pick a remaining element...
    randomIndex = Math.floor(Math.random() * currentIndex);
    currentIndex -= 1;

    // And swap it with the current element.
    temporaryValue = array[currentIndex];
    array[currentIndex] = array[randomIndex];
    array[randomIndex] = temporaryValue;
  }

  return array;
}

function randomelement(arr) {
    var item = arr[Math.floor(Math.random()*arr.length)];
    return item;
}

function depthcharge (role,state, library, start, moves) {
  // console.log('in depth charge')
    if (findterminalp(state,library)) {
      // console.log(findreward(role,state,library))
      var reward = parseInt(findreward(role,state,library));
      console.log("found end state: " + reward);
      return reward;
    }

    const elapsed = Date.now() - start;
    if (elapsed >= ((playclock * 1000) - padtime)) {
      return 0;
    }

    var move = seq();
    for (var i=0; i<roles.length; i++) {
      var options = findlegals(roles[i],state,library);
      move[i] = randomelement(options)
    };
    var newstate = simulate(move,state, library);

    return depthcharge(role,newstate, library, start, moves + 1);
 }

function maxscoresingle(role, state, library, level)
{
  //console.log("On level " + level + " and state" + state)
  if (findterminalp(state, library))
     {return parseInt(findreward(role, state, library))};

  if (level >= limit) {return montecarlo(role,state,3,library)};
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


function bestmovemulti(role, state, library, start){
    // find all legal moves

    var actions = shuffle(findlegals(role, state, library));
    var usefulActions = [];
    var action = actions[0];
    var score = 0;

    console.log('excluding bad moves');
    // Exclude losing moves 
    for (var i = 0; i < actions.length; i++) {
        const elapsed = Date.now() - start;
        if (elapsed >= ((playclock * 1000) - padtime)) {
          return [action, score];
        }
        var opponentState = simulate([actions[i]], state, library);
        if (findterminalp(opponentState, library) && findreward(role, opponentState, library) == 100) {
          return [actions[i], 150];
        }
        var opponent = findopponent(role, library);
        opponentMoves = findlegals(opponent, opponentState, library);
        var opponentWins = false;
        for (var j = 0; j < opponentMoves.length; j++) {
            var nextState = simulate([opponentMoves[j]], opponentState, library); 
            if (findterminalp(nextState, library) && findreward(opponent, nextState, library) == 100) {
                opponentWins = true
                break
            }
        }
        if (!opponentWins) {
           usefulActions.push(actions[i])
        }

    }

    console.log('done excluding');
    // iterate through all legal moves (that aren't losing moves)
    for (var i = 0; i < usefulActions.length; i++) {
      // find minimax score if we make current move
      var result = minscore(role, usefulActions[i], state, library, 1, start); 
      // bound at max score
      if (result == 100){
          return [usefulActions[i], 100];
      }
      // keep the best action
      // console.log('current action: ' + action[2] + ': ' + score + ', new action: ' + usefulActions[i][2] + ': ' + result);
      if (result > score){
          score = result;
          action = usefulActions[i];
      }
    }

    return [action, score];
}


function minscore(role, action, state, library, level, start){
    // get opponent's role
    var opponent = findopponent(role, library);
    // find all legal opponent moves
    var actions = findlegals(opponent, state, library);

    var score = 100;

    // iterate through opponent moves
    for (var i = 0; i < actions.length; i++){
    	var move;
    	if (role == roles[0]){
    	    move = [action, actions[i]];
    	}
    	else {
    	    move = [actions[i], action];
    	}
    	// compute next state
    	var newstate = simulate(move, state, library); 
    	
    	var result = maxscoremulti(role, newstate, library, level + 1, start);

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


function maxscoremulti(role, state, library, level, start){
    // determine if end state
    if (findterminalp(state, library)){
	     return parseInt(findreward(role, state, library));
    }

    // find legal actions 
    var actions = findlegals(role, state, library);
    var score = 0;

    const elapsed = Date.now() - start;
    if (elapsed >= ((playclock * 1000) - padtime)) {
      return 0;
    }

    if (level >= limit) {
      return montecarlo(role,state, depthchargelimit,library, start);
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
