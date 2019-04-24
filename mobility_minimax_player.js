//==============================================================================
// mobility_minimax_player.js
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
const padtime = 7000;

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
  const start = Date.now();
  if (roles.length > 1) {
    return bestmovemulti(role, state, library, start);
  } else {
    return bestmovesingle(role, state, library, start);
  }}

function bestmovesingle(role, state, library, start) {


  var statesQueue = []
  var actions = findlegals(role, state, library);
  var score = 0;
  var timeRanOut = false

  // Initialize queue with best next states from initial state
  for (var i = 0; i < actions.length; i++) {
    var nextState = simulate([actions[i]], state, library)
    statesQueue.push([nextState, actions[i]])
  }


  var bestAction = actions[0]
  while (statesQueue.length !== 0) {

         // Populate the queue with the next states (state, initialAction)
         var [currentState, associatedAction] = statesQueue.shift()
         var nextActions = findlegals(role, currentState, library);
         for (var i = 0; i < nextActions.length; i++) {
             var nextState = simulate([nextActions[i]], currentState, library)
             statesQueue.push([nextState, associatedAction])
         }

         // For current state, check the result, if terminal or if time ran out return heuristic
         var result = -1
         if (findterminalp(currentState, library))
         {
              result = parseInt(findreward(role, currentState, library))
         };

         const elapsed = Date.now() - start;
         if (elapsed >= ((playclock * 1000) - padtime)) {
             result = actions.length;
             timeRanOut = true;
         }

         // If result is hundred, return associatedAction
         if (result == 100) {
             bestAction = associatedAction
             break;
         }

         // If the result is better than the current score, replace the initialAction
         if (result>score) {
            score = result
            bestAction = associatedAction
         }

         if (timeRanOut) {
            break;
         }
    };
    return bestAction[2]
}


function bestmovemulti(role, state, library, start){
    // find all legal moves
    var actions = findlegals(role, state, library);

    var action = actions[0];
    var score = 0;

    // iterate through all legal moves
    for (var i = 0; i < actions.length; i++){
	// find minimax score if we make current move
	var result = minscore(role, actions[i], state, library, start); 
	// bound at max score
	if (result == 100){
	    return actions[i][2];
	}
	// keep the best action
	if (result > score){
	    score = result;
	    action = actions[i];
	}
    }

    return action[2];
}


function minscore(role, action, state, library, start){
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
	else{
	    move = [actions[i], action];
	}
	// compute next state
	var newstate = simulate(move, state, library); 
	
	var result = maxscoremulti(role, newstate, library, start);
	// bound at min score
	if (result == 0){
	    return 0;
	}
	// keep lowest score
	if (result < score) {
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


function maxscoremulti(role, state, library, start){
    // determine if end state
    if (findterminalp(state, library)){
	return findreward(role, state, library);
    }

  const elapsed = Date.now() - start;
  if (elapsed >= ((playclock * 1000) - padtime)) {
    return 0;
  }

    // find legal actions 
    var actions = findlegals(role, state, library);
    var score = 0;

    // iterate through actions
    for (var i = 0; i < actions.length; i++){
	var result = minscore(role, actions[i], state, library, start); 
	// bound at max score
	if (result == 100){
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
