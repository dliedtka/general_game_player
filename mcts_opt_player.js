//==============================================================================
// mcts_opt_player.js
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
eval(fs.readFileSync('complier.js') + '');
// eval(fs.readFileSync('grounder.js') + '');
// eval(fs.readFileSync('optimizer.js') + '');
// eval(fs.readFileSync('winnow.js') + '');

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
var roles2 = seq()
var state = null;
const padtime = 2500;
var interstates = false;
var cache;
var first_move = true;
var tree = {};

//------------------------------------------------------------------------------

function info () {
	return 'ready'
}

function start (id,r,rs,sc,pc)
 {matchid = id;
  library = definemorerules(seq(),rs);
  // library = definemorerules([],prunerules(library));
  eval.call(null,compile(library));
  role = r;
  roles = findroles(library);
  state = findinits(library);
  startclock = sc;
  playclock = pc;
  starttime = Date.now();
  roles2 = fix_roles(role);
  tree = {};
  first_move = true;

  const start_time = Date.now();
  headstart(role, state, library, start_time);

  return 'ready'}


function headstart(role, state, library, start_time){

    // create game tree (node)
    // start with first role
    start_role_idx = 0;
    var clock = playclock;
    // a node has a state, role whose turn it is, parent node, a sequence of children nodes, num_vists, total_utility
    if (first_move){
    	cache = generate_node(state, start_role_idx, "root", library, seq(), "init");
    	first_move = false;
    	var root = cache;
      clock = startclock;
    }
    else{
    	advance_cache(role, state, library);
    	var root = cache;
    }

    // repeat until out of time
    while((Date.now() - start_time) < (clock * 1000 - padtime)){

	// selection
	current_node = select(root, library);

	// expansion 
	expand(current_node, library);

	// simulation
	var end_utility = simulation(role, library, current_node);

	// backpropogation 
	backpropagate(current_node, end_utility, true, role);

    }
    
    // more logging
    var elapsed = (Date.now() - start_time) / 1000;
    console.log("" + root.num_visits + " games simulated in " + elapsed + " seconds; " + (root.num_visits/elapsed) + " simulations per second");
    
    return;
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
      console.log(options);
      return 0;
      move[i] = randomelement(options)
    };
    var newstate = simulate(move,state, library);
    return depthcharge(role,newstate, library);
}

function play (id,move){
    const start_time = Date.now();
    if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
    roles2 = fix_roles(role);
    return bestmove(role, state, library, start_time);
}


function randomelement(arr) {
    var item = arr[Math.floor(Math.random()*arr.length)];
    return item;
}


function fix_roles(role){
    var new_roles = roles.slice();

    for (var player_idx = 0; player_idx < roles.length; player_idx++){
	if (roles[player_idx] == role){
	    break;
	}
    }

    new_roles[0] = roles[player_idx];
    new_roles[player_idx] = roles[0];

    return new_roles;
}


function swap_back(move){
    var new_move = move.slice();

    for (var player_idx = 0; player_idx < roles.length; player_idx++){
	if (roles[player_idx] == role){
	    break;
	}
    }

    new_move[0] = move[player_idx];
    new_move[player_idx] = move[0];

    return new_move;
}


// best move
function bestmove(role, state, library, start_time){
    var actions = findlegals(role, state, library);
    if (actions.length == 1){
    	headstart(role, state, library, start_time);
    	return actions[0][2];
    }
    
    return mcts(role, state, library, start_time);
}

function check_bad_state(action, state, library, role) {
	var opponentState = simulate([action], state, library);
    if (findterminalp(opponentState, library) && findreward(role, opponentState, library) == 100) {
      return 2;
    }
    var current_idx = 0;
    for (var j = 0; j < roles.length; j++) {
      if (role == roles[j]) {
        current_idx = j + 1;
        if (current_idx == roles.length) {
          current_idx = 0;
        }
        break;
      }
    }

    var opponentWins = false;
    while (roles[current_idx] != role) {
      var opponent = roles[current_idx];
      opponentMoves = findlegals(opponent, opponentState, library);
      for (var j = 0; j < opponentMoves.length; j++) {
          var nextState = simulate([opponentMoves[j]], opponentState, library); 
          if (findterminalp(nextState, library) && findreward(opponent, nextState, library) == 100) {
              opponentWins = true;
              break;
          }
      }
      if (opponentWins) {
        break;
      }
      current_idx += 1;
      if (current_idx == roles.length) {
        current_idx = 0;
      }
    }
    if (opponentWins) {
    	return 1;
    } else {
    	return 0;
    }
}


// monte carlo tree search
function mcts(role, state, library, start_time){
    
    // create game tree (node)
    // start with first role
    start_role_idx = 0;

    // a node has a state, role whose turn it is, parent node, a sequence of children nodes, num_vists, total_utility
	advance_cache(role, state, library);
	var root = cache;

    // repeat until out of time
    while((Date.now() - start_time) < (playclock * 1000 - padtime)){
	
	// selection
	current_node = select(root, library);

	// expansion 
	expand(current_node, library);

	// simulation
	var end_utility = simulation(role, library, current_node);

	// backpropogation 
	backpropagate(current_node, end_utility, true, role);
    }

    // choose highest average move or most visited (almost always will be the same)
    var score = 0;
    var action = root.children[0].action;
    var j = 0;
    while (j < root.children.length && check_bad_state(root.children[j].action, state, library, role) === 1) {
    	j += 1;
    }
    if (j < root.children.length) {
    	action = root.children[j].action;
    }
    for (var i = 0; i < root.children.length; i++){
    if (roles.length > 1) {
	    const potential_bad = check_bad_state(root.children[i].action, state, library, role);
	    if (potential_bad === 1) {
			console.log("Losing action... skipping");
			continue;
		} else if (potential_bad === 2) {
			return root.children[i].action[2];
		}
	}
	var newscore = root.children[i].total_utility / root.children[i].num_visits;

	// logging
	console.log("action: " + root.children[i].action + " utility: " + root.children[i].total_utility + " numvisits: " + root.children[i].num_visits + " score: " + newscore);

	if (newscore > score){
	    score = newscore;
	    action = root.children[i].action;
	}
    }

    // more logging
    var elapsed = (Date.now() - start_time) / 1000;
    console.log("" + root.num_visits + " games simulated in " + elapsed + " seconds; " + (root.num_visits/elapsed) + " simulations per second");
    console.log("current projected utility: " + score);

    return action[2];
}


function find_next_role_idx(current_role_idx){
    for (var i = 0; i < roles2.length; i++){
	if (roles2[i] == roles2[current_role_idx]){
	    if (i == roles2.length - 1){
		return 0;
	    }
	    else{
		return i+1;
	    }
	}
    }
}


function advance_cache(role, current_state, library){

    tree[JSON.stringify([role, current_state])].parent = "root";
    cache = tree[JSON.stringify([role, current_state])];
    // get previous node
    //var previous_state = cache.state;
 //    var current_node = cache;

 //    // randomly traverse until you get to current state
 //    while (JSON.stringify(current_node.state) !== JSON.stringify(current_state)){
	// current_node = cache;
	// for (var i = 0; i < roles2.length; i++){
	//     current_node = randomelement(current_node.children);
	// }
 //    }

 //    // set current node to root
 //    current_node.parent = "root";
 //    // set cache to node associated with current state
 //    cache = current_node;
}


// a node has a state, role whose turn it is, parent node, a sequence of children nodes, num_vists, total_utility, a move to make
function generate_node(state, current_role_idx, parent, library, move, last_action){
    var node = {};

    node["state"] = state;

    node["current_role_idx"] = current_role_idx; // index of which role is selecting a move at current node
    node["parent"] = parent;
    if (findterminalp(state, library)){
	node["children"] = "terminal";
    }
    else{
	node["children"] = seq();
    }
    node["num_visits"] = 0;
    node["total_utility"] = 0;
    node["move"] = move; // sequence that will be the next move (every role must make a move, simulate to new state after roles2.length nodes)
    node["action"] = last_action; // action from parent node that led to this node
    tree[JSON.stringify([roles2[current_role_idx], state])] = node;
    return node;
}


function select(node, library){
    
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
	var newscore = selectfn(node.children[i]);
	if (newscore > score){
	    score = newscore; 
	    result = node.children[i];
	}
    }

    return select(result, library);
}


function selectfn(node){
	C = 40.0;
	if (roles.length === 1) {
		C = 100.0;
	}
    return node.total_utility / node.num_visits + C * Math.sqrt(2.0 * Math.log(node.parent.num_visits) / node.num_visits);
    //return Math.random(); // used for some debugging
    // could try other selectfn functions
}


// only simulate to new state if current role is last role (because then all roles have added a new action to move)
function expand(node, library){
    
    // auto return an end state (no states left to add to game tree)
    if (node.children === "terminal"){
	return true;    
    }

    var actions = findlegals(roles2[node.current_role_idx], node.state, library);

    // add a node for all successors (one successor for each legal action)
    for (var i = 0; i < actions.length; i++){

	// set move to action for corresponding role
	var newmove = node.move.slice(); // need to use slice to make a new copy of move for the new node (arrays are reference values in javascript)
	newmove[node.current_role_idx] = actions[i];

	// only simulate for last role
	if (find_next_role_idx(node.current_role_idx) == 0){
	    var newstate = simulate(swap_back(newmove), node.state, library); 
	}
	else{
	    var newstate = node.state;
	}
	var newnode = generate_node(newstate, find_next_role_idx(node.current_role_idx), node, library, newmove, actions[i]);
	node.children[node.children.length] = newnode;
    }

    return true;
}


function simulation(role, library, node){

    var first_loop = true;

    var newstate = node.state;
    while (!findterminalp(newstate,library)){

	// for debugging simulation of games
	//if (first_loop){
	//    console.log("\nsimulating");
	//    console.log("state: " + node.state);
	//    console.log("role: " + node.current_role_idx);
	//    console.log("action: " + node.action);
	//   console.log("move: " + node.move);
	//}

	// random move with some exceptions
	// on the first iteration of the while loop only:
	// random move for undecided roles only
	// if node n has control over current node, all nodes less than n have decided on an action and stored in node.move
	// don't want to overwrite those actions just because we have yet to transition to a new state
	var move = seq();
	for (var i = 0; i < roles2.length; i++){
	    if (first_loop && (i < node.current_role_idx)){
		move[i] = node.move[i];
	    }
	    else{
		var actions = findlegals(roles2[i], newstate, library);
		move[i] = randomelement(actions);
	    }
	}
	
	// more debugging
	//console.log("random move: " + move);
	//console.log("new state: " + newstate);

	newstate = simulate(swap_back(move), newstate, library);

	first_loop = false;
    }

    // more debugging
    //console.log("reward: " + findreward(role,newstate,library));
    //console.log("end simulating\n");

    return parseInt(findreward(role, newstate, library));
}


function backpropagate(node, score, first_call, role){

    // for debugging min/max nodes
    //console.log("backprop");
    //console.log("state: " + node.state);
    //console.log("action: " + node.action);
    //console.log("role: " + node.current_role_idx);
    //console.log("prev util: " + node.total_utility);
    //console.log("prev visits: " + node.num_visits);
    //console.log("prev score: " + node.total_utility / node.num_visits);
    
    if (roles2.length == 1){
	node.num_visits = node.num_visits + 1;
	node.total_utility = node.total_utility + score;
	if (node.parent !== "root"){
	    backpropagate(node.parent, score, false, role);
	}
    }


    // multiple roles, backprop value is min of opponent actions, max for player node?
    else{
	node.num_visits = node.num_visits + 1;

	// for "result" node we just add achieved score
	if (first_call){
	    node.total_utility = node.total_utility + score;
	}

	// player controlled nodes add max utility per visit of children
	else if (roles2[node.current_role_idx] == role){
	    var maxscore = 0;
	    for (var i = 0; i < node.children.length; i++){
		// don't look at unvisited children (0/0 will propogate up, cause error)
		if (node.children[i].num_visits == 0){
		    continue;
		}
		else{
		    var newscore = node.children[i].total_utility / node.children[i].num_visits;
		    if (newscore > maxscore){
			maxscore = newscore;
		    }
		}
	    }
	    node.total_utility = node.total_utility + maxscore;
	}

	// opponent controlled nodes add min utility per visit of children
	else{
	    var minscore = 100;
	    for (var i = 0; i < node.children.length; i++){
		if (node.children[i].num_visits == 0){
		    continue;
		}
		else{
		    var newscore = node.children[i].total_utility / node.children[i].num_visits;
		    if (newscore < minscore){
			minscore = newscore;
		    }
		}
	    }
	    node.total_utility = node.total_utility + minscore;
	}

	// more debugging
	//console.log("after util: " + node.total_utility);
	//console.log("after visits: " + node.num_visits);
	//console.log("after score: " + node.total_utility / node.num_visits);
	//if (node.parent !== "root"){
	//    console.log("now calling state: " + node.parent.state);
	//    console.log("now calling action: " + node.parent.action);
	//    console.log("now calling role: " + node.parent.current_role_idx);
	//    console.log(" ");
	//}
	//else{
	//    console.log(" ");
	//}

	if (node.parent !== "root"){
	    backpropagate(node.parent, score, false, role);
	}
    }

    return true;
}

  
function abort (id)
  {return 'done'}

function stop (id,move)
  {return 'done'}

//==============================================================================
// comp.js
//==============================================================================
//==============================================================================
// Basics
//==============================================================================

function findroles (rules)
 {return basefinds('R',seq('role','R'),seq(),rules)}

function findbases (rules)
 {return basefinds('P',seq('base','P'),seq(),rules)}

function findinputs (rules)
 {return basefinds('A',seq('input','A'),seq(),rules)}

function findinits (rules)
 {return basefinds(seq('true','P'),seq('init','P'),seq(),rules)}

function findlegalp (role,action,facts,rules)
 {return $legal$bb$(role,action,facts,rules)[1]}

function findlegalx (role,facts,rules)
 {return seq('does',role,$legal$bf$(role,facts,rules))}

function findlegals (role,facts,rules)
 {return zniquify($$legal$bf$$(role,facts,rules)).map(x => seq('does',role,x))}

function findnexts (facts,rules)
 {return vniquify($$next$f$$(facts,rules)).map(x => seq('true',x))}

function findterminalp (facts,rules)
 {return $terminal$$(facts,rules)}

function findreward (role,facts,rules)
 {return $goal$bf$(role,facts,rules)}


//------------------------------------------------------------------------------

function simulate (move,state,rules)
 {return findnexts(move.concat(state),rules)}

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
// Epilog parameters
//==============================================================================

indexing = true;
dataindexing = false;
ruleindexing = true;

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
