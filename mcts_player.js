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
//var limit = 1;
const padtime = 2500;
//var depthchargelimit = 8;

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
    const start_time = Date.now();
    //depthchargelimit = 8;
    //if (roles.length == 1) {
    //  limit = 3;
    //}
    if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
    return bestmove(role, state, library, start_time);
}


function randomelement(arr) {
    var item = arr[Math.floor(Math.random()*arr.length)];
    return item;
}


// best move
function bestmove(role, state, library, start_time){
    return mcts(role, state, library, start_time);
}


// monte carlo tree search
function mcts(role, state, library, start_time){
    
    // create game tree (node)
    // start with first role
    current_role_idx = 0;
    
    // a node has a state, role whose turn it is, parent node, a sequence of children nodes, num_vists, total_utility
    var root = generate_node(state, current_role_idx, "root", library, seq(), "init");

    // repeat until out of time
    while((Date.now() - start_time) < (playclock * 1000 - padtime)){

	// selection
	current_node = select(root);

	// expansion //******* need to check this and simulation, should simulation and backpropogate be getting current_node?
	expand(node, current_role_idx);

	// simulation
	var end_utility = simulation(roles[current_node.current_role_idx], current_node.state, library);

	// backpropogation
	backpropogate(current_node, end_utility);

	// next role
	current_role_idx = find_next_role_idx(current_role_idx);
    }

    // choose highest average move or most visited (almost always will be the same)
    var score = 0;
    var action = node.children[0].action;
    for (var i = 0; i < node.children; i++){
	var newscore = node.children[i].total_utility / node.children[i].num_visits;
	if (newscore > score){
	    score = newscore;
	    action = node.children[i].action;
	}
    }
    
    return action;
}


function find_next_role_idx(current_role_idx){
    for (var i; i < roles.length; i++){
	if (roles[i] == roles[current_role_idx]){
	    if (i == roles.length - 1){
		return 0;
	    }
	    else{
		return i+1;
	    }
	}
    }
}


// a node has a state, role whose turn it is, parent node, a sequence of children nodes, num_vists, total_utility, a move to make
function generate_node(state, current_role_idx, parent, library, move, last_action){
    var node;

    node["state"] = state;
    node["current_role_idx"] = current_role_idx;
    node["parent"] = parent;
    if (findterminalp(state, library)){
	node["children"] = "terminal";
    }
    else{
	node["children"] = seq();
    }
    node["num_visits"] = 0;
    node["total_utility"] = 0;
    node["move"] = move;
    node["action"] = last_action;

    return node;
}


function select(node){

    if (node.num_visits == 0){
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
	var newscore = selectfn(node.children[i]);
	if (newscore > score){
	    score = newscore; 
	    result = node.children[i];
	}
    }
    
    return select(result)
}


function selectfn(node){
    return node.total_utility / node.num_visits + Math.sqrt(2 * Math.log(node.parent.num_visits) / node.num_visits);
}


// only simulate if current role is last role
function expand(node, current_role_idx, library){
    var actions = findlegals(roles[current_role_idx], node.state, library);
    
    for (var i = 0; i < actions.length; i++){
	// set move to action for corresponding role
	node.move[current_role_idx] = actions[i]

	if (find_next_role_idx(current_role_idx) == roles[0]){
	    var newstate = simulate(node.move, node.state); 
	}
	else{
	    var newstate = node.state;
	}
	var newnode = generate_node(newstate, find_next_role_idx(current_role_idx), node, library, node.move, actions[i]);
	node.children[node.children.length] = newnode;
    }
    
    return true;
}


function simulation(role, state, library){
    var newstate = state;

    while (!findterminalp(newstate,library)){

	var move = seq();
	for (var i = 0; i < roles.length; i++){
	    var actions = findlegals(roles[i], newstate, library);
	    move[i] = randomelement(actions);
	}

	newstate = simulate(move, newstate, library);
    }

    return parseInt(findreward(role, newstate, library));
}


function backpropogation(node, score){
    node.num_visits = node.num_visits + 1;
    node.total_utility = node.total_utility + score;
    if (node.parent !== "root"){
	backpropagate(node.parent,score);
    }
    return true;
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
