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
const padtime = 2500; // TODO: decrease to one sec?
var cache = {};
var first_run = true;
var nomove_mcts = false;

//------------------------------------------------------------------------------

function info ()
 {return 'ready'}

function start (id,r,rs,sc,pc) // TODO: headstart
 {matchid = id;
  library = definemorerules(seq(),rs);
  role = r;
  roles = findroles(library);
  state = findinits(library);
  startclock = sc;
  playclock = pc;

  const start_time = Date.now();
  headstart(role, state, library, start_time);

  return 'ready'}


function headstart(role, state, library, start_time){
    nomove_mcts = true;
    mcts(role, state, library, start_time);
    nomove_mcts = false;
}


function play (id,move){
    const start_time = Date.now();
    if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
    return bestmove(role, state, library, start_time);
}


function randomelement(arr) {
    var item = arr[Math.floor(Math.random()*arr.length)];
    return item;
}


// best move
function bestmove(role, state, library, start_time){
    // TODO: advance cache

    var actions = findlegals(role, state, library);
    if (actions.length == 1){
	nomove_mcts = true;
	mcts(role, state, library, start_time);
	nomove_mcts = false;
	return actions[0][2]; // TODO: run mcts until run out of time
    }
    
    return mcts(role, state, library, start_time);
}


// monte carlo tree search
function mcts(role, state, library, start_time){
    
    var role_idx = 0;
    while (roles[role_idx] !== role){
	role_idx++;
    }


    // TODO: advance cache, first visit should generate node
    // create game tree (node), idea 3 so one node for each state
    // a node has a state, parent node, a sequence of children nodes, num_vists, total_utility for each role
    //var root = generate_node(state, "root", "init", library);
    // first run only 
    if (first_run){
	generate_node(state, "root", "init", library);
	first_run = false;
    }
    //console.log("in function: " + cache[node.state].state);
    //console.log(cache[node.state].total_utility);
    //console.log(cache[node.state].num_visits);
    var root = cache[state];
    var start_visits = root.num_visits;
    
    var counter = 0;
    // repeat until out of time
    while((Date.now() - start_time) < (playclock * 1000 - padtime)){

	// selection
	current_node = select(root, library, role_idx);

	// expansion 
	expand(current_node, library);

	// simulation
	var end_reward = simulation(role, library, current_node);

	// backpropogation 
	backpropagate(current_node, end_reward, true, library);
    }

    if (!nomove_mcts){
	// choose highest average move or most visited (almost always will be the same), no minimax assumption
	var action = best_action(root, role_idx, library, true);
    }

    // more logging
    var elapsed = (Date.now() - start_time) / 1000;
    console.log("" + (root.num_visits - start_visits) + " games simulated in " + elapsed + " seconds; " + ((root.num_visits - start_visits)/elapsed) + " simulations per second");
    
    if (nomove_mcts){
	return;
    }
    else{
	return action[2];
    }
}


// a node has a state, parent node, a sequence of children nodes, num_vists, total_utility for each role; no move that led to state so we can combine identical states in cache
function generate_node(state, parent, library){
    
    // if state already in keyspace of cache, return
    if (state in cache){
	return;
    }

    var node = {};

    node["state"] = state;

    node["parent"] = parent;

    if (findterminalp(state, library)){
	node["children"] = "terminal";
    }
    else{
	node["children"] = seq();
    }
    
    node["num_visits"] = 0;
    
    node["total_utility"] = seq();
    for (var i = 0; i < roles.length; i++){
	node.total_utility[i] = 0;
    }

    cache[node.state] = node;
    
    return;
}


function select(node, library, role_idx){
    if (node.num_visits == 0){
	return node;
    }
    
    // no children to explore (reached a leaf of game tree)
    if (node.children === "terminal"){
	return node;
    }

    for (var i = 0; i < node.children.length; i++){
	if (node.children[i].num_visits == 0){
	    return node.children[i];
	}
    }

    var score = 0;
    var result = node;
    
    for (var i = 0; i < node.children.length; i++){
	var newscore = selectfn(node.children[i], role_idx);
	if (newscore > score){
	    score = newscore; 
	    result = node.children[i];
	}
    }

    return select(result, library, role_idx);
}


function selectfn(node, role_idx){
    return node.total_utility[role_idx] / node.num_visits + Math.sqrt(40 * Math.log(node.parent.num_visits) / node.num_visits);
    //return Math.random(); // used for some debugging
    // could try other selectfn functions
}


function expand(node, library){
    
    // auto return an end state (no states left to add to game tree)
    if (node.children === "terminal"){
	return true;    
    }

    // generate all possible move combinations
    var moves = generate_moves(node.state, library);

    for (var i = 0; i < moves.length; i++){
	var newstate = simulate(moves[i], node.state, library);
	//var newnode = generate_node(newstate, node, library);
	//node.children[node.children.length] = newnode;
	generate_node(newstate, node, library);
	node.children[node.children.length] = cache[newstate];
    }

    return true;
}


// recursively generate all possible moves
function generate_moves(state, library){
    return generate_moves_helper(state, library, 0, seq(), seq());
}

function generate_moves_helper(state, library, current_role_idx, moves, move){
 
    // end case
    if (current_role_idx == roles.length){
	moves[moves.length] = move.slice();
	return true;
    }
    
    var current_role = roles[current_role_idx];
    var actions = findlegals(current_role, state, library);

    for (var i = 0; i < actions.length; i++){
	var newmove = move.slice();
	newmove[current_role_idx] = actions[i];

	generate_moves_helper(state, library, current_role_idx + 1, moves, newmove);
    }

    return moves;
}


function simulation(role, library, node){ // TODO: might not need role, return utility for all roles

    var newstate = node.state;
    while (!findterminalp(newstate,library)){

	// for debugging simulation of games
	//if (first_loop){
	//    console.log("\nsimulating");
	//    console.log("state: " + node.state);
	//}

	// random move 
	var move = seq();
	for (var i = 0; i < roles.length; i++){
	    var actions = findlegals(roles[i], newstate, library);
	    move[i] = randomelement(actions);
	}
	
	// more debugging
	//console.log("random move: " + move);
	//console.log("new state: " + newstate);

	newstate = simulate(move, newstate, library);
    }

    // more debugging
    //console.log("reward: " + findreward(role,newstate,library));
    //console.log("end simulating\n");

    var reward = seq();
    for (var i = 0; i < roles.length; i++){
	reward[i] = parseInt(findreward(roles[i], newstate, library));
    }
    return reward;
}


function backpropagate(node, scores, first_call, library){

    node.num_visits++;

    // for "result" node we just add achieved score
    if (first_call){
	for (var i = 0; i < roles.length; i++){
	    node.total_utility[i] += scores[i];
	}
    }

    else{
	// find the action that maximizes utility for each role
	var best_move = seq();
	for (var i = 0; i < roles.length; i++){
	    best_move[i] = best_action(node, i, library, false);
	}

	var best_state = simulate(best_move, node.state, library);

	// find the child that matches the best state

	for (var i = 0; i < node.children.length; i++){
	    if (JSON.stringify(best_state) == JSON.stringify(node.children[i].state)){
		if (node.children[i].num_visits > 0){
		    for (var j = 0; j < roles.length; j++){
			node.total_utility[j] += node.children[i].total_utility[j] / node.children[i].num_visits;
		    }
		}
		else{
		    console.log("should probably pick a random visited node")
		}
	    }
	}
    }

    if (node.parent !== "root"){
	backpropagate(node.parent, scores, false, library);
    }

    return true;
}


function best_action(node, role_idx, library, verbose){
    var actions = findlegals(roles[role_idx], node.state, library);

    if (actions.length === 1){
	return actions[0];
    }

    else{
	// iterate through actions
	var score = 0;
	var action = actions[0];
	for (var i = 0; i < actions.length; i++){
	    var tempscore = 0;
	    var counter = 0;

	    // create list of all possible newstates with that action
	    var possible_moves = generate_moves(node.state, library);
	    
	    var action_moves = seq();
	    for (var k = 0; k < possible_moves.length; k++){
		if (JSON.stringify(possible_moves[k][role_idx]) == JSON.stringify(actions[i])){
		    action_moves[action_moves.length] = possible_moves[k];
		}
	    }
	    
	    var newstates = seq();
	    for (var k = 0; k < action_moves.length; k++){
		newstates[k] = JSON.stringify(simulate(action_moves[k], node.state, library));
	    }

	    // check if each child state is in new states
	    for (var j = 0; j < node.children.length; j++){

		if (newstates.indexOf(JSON.stringify(node.children[j].state)) > -1 && node.children[j].num_visits > 0){

		    tempscore += node.children[j].total_utility[role_idx]; 
		    counter += node.children[j].num_visits;
		}
	    }

	    if (counter == 0){
		var newscore = 0;
	    }
	    else{
		var newscore = tempscore / counter;
	    }
	    
	    // logging
	    if (verbose){
		console.log("action: " + actions[i] + " utility: " + tempscore + " numvisits: " + counter + " score: " + newscore);
	    }

	    if (newscore > score){
		score = newscore;
		action = actions[i];
	    }
	}

	return action;
    }
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
