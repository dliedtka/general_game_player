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
eval(fs.readFileSync('complier.js') + '');

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
const padtime = 1000; // TODO: decrease to one sec?
var cache = {};
var first_run = true;
var nomove_mcts = false;
var states_visited;
var clock;
var num_generates = 0;
var turnbased = false;
var is_coop = true;
var use_heuristics = false;

//------------------------------------------------------------------------------

function info() {
  return 'ready'
}

function start(id, r, rs, sc, pc) // TODO: headstart
{
  cache = {};
  first_run = true;
  use_heuristics = false;
  matchid = id;
  library = definemorerules(seq(), rs);
  role = r;
  roles = findroles(library);
  state = findinits(library);
  library = definemorerules([], prunerulesubgoals(library));
  library = definemorerules([], prunerules(library));
  library = definemorerules([], fixrules(library));
  eval.call(null, compile(library));
  turnbased = is_turnbased(state, library);
  is_coop = true;

  startclock = sc;
  playclock = pc;

  clock = startclock;
  const start_time = Date.now();
  var count = 0;
  while (true) {
    const elapsed = Date.now() - start_time;
    if (elapsed >= 1500) {
      break;
    }
    var role_rewards = depthcharge(role, state, library, start_time);
    var rew = role_rewards[0];
    for (var r = 0; r < roles.length; r++) {
      if (role_rewards[r] !== rew) {
        is_coop = false;
      }
    }
    count += 1;
  }

  const count_over_time = 1.0 * count / 1.5;
  console.log(count_over_time);
  if (count_over_time < 5) {
    use_heuristics = true;
  }


  console.log(turnbased);
  console.log(is_coop);
  headstart(role, state, library, start_time);

  return 'ready'
}

function depthcharge(role, state, library, starttime) {
  if (findterminalp(state, library)) {
    //console.log("reward")
    //console.log(findreward(role,state,library))
    var role_rewards = [];
    for (var r = 0; r < roles.length; r++) {
      role_rewards.push(parseInt(findreward(roles[r], state, library)));
    }
    return role_rewards;
  };

  // const elapsed = Date.now() - starttime;
  // if (elapsed >= (3000)) {
  //   return 0;
  // }

  var move = seq();
  for (var i = 0; i < roles.length; i++) {
    var options = findlegals(roles[i], state, library);
    move[i] = randomelement(options)
  };
  var newstate = simulate(move, state, library);
  return depthcharge(role, newstate, library);
}

//==============================================================================
// optimize
//==============================================================================
//------------------------------------------------------------------------------
// prunesubgoals
//------------------------------------------------------------------------------

function prunerulesubgoals(rules) {
  var newrules = seq();
  for (var i = 0; i < rules.length; i++) {
    if (symbolp(rules[i])) {
      newrules.push(rules[i])
    } else if (rules[i][0] == 'rule') {
      newrules.push(prunesubgoals(rules[i]))
    } else {
      newrules.push(rules[i])
    }
  };
  return newrules
}

function prunesubgoals(rule) {
  var vl = vars(rule[1]);
  var newrule = seq('rule', rule[1]);
  for (var i = 2; i < rule.length; i++) {
    if (!symbolp(rule[i]) && rule[i][0] === 'not') {
      newrule.push(rule[i]);
      continue
    };
    if (!symbolp(rule[i]) && rule[i][0] === 'distinct') {
      newrule.push(rule[i]);
      continue
    };
    if (!pruneworthyp(newrule.slice(2).concat(rule.slice(i + 1)), rule[i], vl)) {
      newrule.push(rule[i])
    }
  };
  return newrule
}

function pruneworthyp(sl, p, vl) {
  vl = varsexp(sl, vl.slice(0));
  var al = seq();
  for (var i = 0; i < vl.length; i++) {
    al[vl[i]] = 'x' + i
  };
  var facts = sublis(sl, al);
  var goal = sublis(p, al);
  return basefindp(goal, facts, seq())
}

function sublis(x, al) {
  if (varp(x)) {
    if (al[x]) {
      return al[x]
    } else return x
  };
  if (symbolp(x)) {
    return x
  };
  var exp = seq();
  for (var i = 0; i < x.length; i++) {
    exp[i] = sublis(x[i], al)
  };
  return exp
}

//------------------------------------------------------------------------------
// prunerules
//------------------------------------------------------------------------------

function prunerules(rules) {
  var newrules = seq();
  for (var i = 0; i < rules.length; i++) {
    if (!subsumedp(rules[i], newrules) &&
      !subsumedp(rules[i], rules.slice(i + 1))) {
      newrules.push(rules[i])
    }
  };
  return newrules
}

function subsumedp(rule, rules) {
  for (i = 0; i < rules.length; i++) {
    if (subsumesp(rules[i], rule)) {
      return true
    }
  };
  return false
}

function subsumesp(p, q) {
  if (equalp(p, q)) {
    return true
  };
  if (symbolp(p) || symbolp(q)) {
    return false
  };
  if (p[0] === 'rule' && q[0] === 'rule') {
    var al = matcher(p[1], q[1]);
    if (al !== false && subsumesexp(p.slice(2), q.slice(2), al)) {
      return true
    }
  };
  return false
};

function subsumesexp(pl, ql, al) {
  if (pl.length === 0) {
    return true
  };
  for (var i = 0; i < ql.length; i++) {
    var bl = match(pl[0], ql[i], al);
    if (bl !== false && subsumesexp(pl.slice(1), ql, bl)) {
      return true
    }
  };
  return false
}

//------------------------------------------------------------------------------
// fixrules
//------------------------------------------------------------------------------

function fixrules(rules) {
  var newrules = seq();
  for (var i = 0; i < rules.length; i++) {
    if (symbolp(rules[i])) {
      newrules.push(rules[i])
    } else if (rules[i][0] === 'rule') {
      newrules.push(fixrule(rules[i]))
    } else {
      newrules.push(rules[i])
    }
  };
  return newrules
}

function fixrules(rules) {
  return rules
}

function fixrule(rule) {
  var vl = seq();
  var sl = rule.slice(2);
  var newrule = seq('rule', rule[1]);
  while (sl.length > 0) {
    var ans = getbest(sl, vl);
    if (ans) {
      newrule.push(ans)
    } else {
      newrule.push(sl[0]);
      vl = varsexp(sl[0], vl);
      sl.splice(0, 1)
    }
  }
  return newrule
}

function getbest(sl, vl) {
  for (var i = 0; i < sl.length; i++) {
    if (groundedp(sl[i], vl)) {
      var ans = sl[i];
      sl.splice(i, 1);
      return ans
    }
  }
  return false
}

function fixrule(rule) {
  var vl = seq();
  var sl = rule.slice(2);
  var newrule = seq('rule', rule[1]);
  while (sl.length > 0) {
    var ans = getbest(sl, vl);
    newrule.push(ans);
    vl = varsexp(ans, vl)
  };
  return newrule
}

function getbest(sl, vl) {
  var varnum = 10000;
  var best = 0;
  for (var i = 0; i < sl.length; i++) {
    var dum = unboundvarnum(sl[i], vl);
    if (dum < varnum && (symbolp(sl[i]) || sl[i][0] !== 'not' || dum === 0)) {
      varnum = dum;
      best = i
    }
  };
  var ans = sl[best];
  sl.splice(best, 1);
  return ans
}

function unboundvarnum(x, vs) {
  return unboundvars(x, seq(), vs).length
}

function unboundvars(x, us, vs) {
  if (varp(x)) {
    if (find(x, vs)) {
      return us
    } else {
      return adjoin(x, us)
    }
  };
  if (symbolp(x)) {
    return us
  };
  for (var i = 0; i < x.length; i++) {
    us = unboundvars(x[i], us, vs)
  };
  return us
}


function headstart(role, state, library, start_time) {
  nomove_mcts = true;
  mcts(role, state, library, start_time);
  nomove_mcts = false;
}


function play(id, move) {
  clock = playclock;
  const start_time = Date.now();
  if (move !== 'nil') {
    state = simulate(doesify(roles, move), state, library)
  };
  return bestmove(role, state, library, start_time);
}


function randomelement(arr) {
  var item = arr[Math.floor(Math.random() * arr.length)];
  return item;
}


// best move
function bestmove(role, state, library, start_time) {
  // TODO: advance cache

  var actions = findlegals(role, state, library);
  if (actions.length == 1) {
    nomove_mcts = true;
    mcts(role, state, library, start_time);
    nomove_mcts = false;
    return actions[0][2]; // TODO: run mcts until run out of time
  }

  return mcts(role, state, library, start_time);
}

function parse_state(state) {
  var parsed = [];
  for (var i = 0; i < state.length; i++) {
    if (state[i][1].includes(role) || state[i][1].includes('step')) {
      parsed.push(state[i]);
    }
  }
  return parsed;
}

// monte carlo tree search
function mcts(curr_role, state, library, start_time) {

  var role_idx = 0;
  if (turnbased) {
    while (findlegals(roles[role_idx], state, library).length === 1) {
      role_idx++;
    }
    curr_role = roles[role_idx];
  } else {
    while (roles[role_idx] !== curr_role) {
      role_idx++;
    }
  }


  // TODO: advance cache, first visit should generate node
  // create game tree (node), idea 3 so one node for each state
  // a node has a state, parent node, a sequence of children nodes, num_vists, total_utility for each role
  //var root = generate_node(state, "root", "init", library);
  // first run only 
  if (first_run) {
    generate_node(state, library);
    first_run = false;
  }
  //console.log("in function: " + cache[node.state].state);
  //console.log(cache[node.state].total_utility);
  //console.log(cache[node.state].num_visits);
  var root = cache[state];
  if (!turnbased && !is_coop) {
    root = cache[parse_state(state)];
  }
  var start_visits = root.num_visits;

  var counter = 0;
  // repeat until out of time

  while ((Date.now() - start_time) < (clock * 1000 - padtime)) {
    states_visited = seq();
    states_visited[states_visited.length] = state;

    // selection
    current_node = select(root, library, role_idx);

    // expansion 
    expand(current_node, library);

    // simulation
    var end_reward = simulation(curr_role, library, current_node);

    // backpropogation 
    backpropagate(states_visited, end_reward);

    counter += 1;
  }

  if (!nomove_mcts) {
    // choose highest average move or most visited (almost always will be the same), no minimax assumption
    var action = best_action(root, role_idx, library);
  }

  // more logging
  var elapsed = (Date.now() - start_time) / 1000;
  console.log("" + (root.num_visits - start_visits) + " games simulated in " + elapsed + " seconds; " + ((root.num_visits - start_visits) / elapsed) + " simulations per second");

  if (nomove_mcts) {
    return;
  } else {
    return action[2];
  }
}


// a node has a state, parent node, a sequence of children nodes, num_vists, total_utility for each role; no move that led to state so we can combine identical states in cache
function generate_node(state, library) {

  // if state already in keyspace of cache, return
  if (state in cache || (!turnbased && !is_coop && parse_state(state) in cache)) {
    return;
  }

  var node = {};

  node["state"] = state;

  if (findterminalp(state, library)) {
    node["children"] = "terminal";
  } else {
    node["children"] = seq();
  }

  node["num_visits"] = 0;

  node["total_utility"] = seq();
  for (var i = 0; i < roles.length; i++) {
    node.total_utility[i] = 0;
  }
  if (!turnbased && !is_coop) {
    cache[parse_state(state)] = node;
  } else {
    cache[node.state] = node;
  }

  return;
}

function is_turnbased(state, library) {
  var turn_based = false;
  var coop = false
  var next_role = 0;
  for (var i = 0; i < roles.length; i++) {
    var num_actions = findlegals(roles[i], state, library).length;
    if (turn_based && num_actions > 1) {
      coop = true;
    } else if (num_actions > 1) {
      turn_based = true;
    }
  }
  return !coop;
}


function select(node, library, role_idx) {
  if (node.num_visits == 0) {
    return node;
  }

  // no children to explore (reached a leaf of game tree)
  if (node.children == "terminal") {
    return node;
  }

  // if (turnbased) {
  //   role_idx = 0;
  //   while (findlegals(roles[role_idx], node.state, library).length === 1) {
  //     role_idx++;
  //   }
  // }

  var score = 0;
  var result = node.children[0];

  for (var i = 0; i < node.children.length; i++) {
    if (node.children[i].num_visits == 0) {
      states_visited[states_visited.length] = node.children[i].state;
      return node.children[i];
    }
    var newscore = selectfn(node.children[i], role_idx, node);
    if (newscore > score) {
      score = newscore;
      result = node.children[i];
    }
  }

  var new_role_idx = role_idx;
  if (turnbased) {
    new_role_idx = role_idx + 1;
    if (new_role_idx == roles.length) {
      new_role_idx = 0;
    }
    // if (findlegals(roles[new_role_idx], result.state, library).length === 1) {
    //   new_role_idx = role_idx;
    // }
  }

  states_visited[states_visited.length] = result.state;
  return select(result, library, new_role_idx);
}


function selectfn(node, role_idx, parent_node) {
  var C = 50.0;
  return node.total_utility[role_idx] / node.num_visits + C * Math.sqrt(Math.log(parent_node.num_visits) / node.num_visits);
  //return Math.random(); // used for some debugging
  // could try other selectfn functions
}


function expand(node, library) {

  // auto return an end state (no states left to add to game tree)
  if (node.children === "terminal") {
    return;
  }

  // generate all possible move combinations
  var moves = generate_moves(node.state, library);

  for (var i = 0; i < moves.length; i++) {
    var newstate = simulate(moves[i], node.state, library);
    //var newnode = generate_node(newstate, node, library);
    //node.children[node.children.length] = newnode;
    generate_node(newstate, library);
    if (!turnbased && !is_coop) {
      node.children[node.children.length] = cache[parse_state(newstate)]
    } else {
      node.children[node.children.length] = cache[newstate];
    }
  }
}


// recursively generate all possible moves
function generate_moves(state, library) {
  return generate_moves_helper(state, library, 0, seq(), seq());
}

function generate_moves_helper(state, library, current_role_idx, moves, move) {

  // end case
  if (current_role_idx == roles.length) {
    moves[moves.length] = move.slice();
    return;
  }

  var current_role = roles[current_role_idx];
  var actions = findlegals(current_role, state, library);

  if (!turnbased && !is_coop && current_role !== role) {
    var newmove = move.slice();
    newmove[current_role_idx] = actions[0];

    generate_moves_helper(state, library, current_role_idx + 1, moves, newmove);
  } else {

    for (var i = 0; i < actions.length; i++) {
      var newmove = move.slice();
      newmove[current_role_idx] = actions[i];

      generate_moves_helper(state, library, current_role_idx + 1, moves, newmove);
    }
  }

  return moves;
}


function simulation(role, library, node) { // TODO: might not need role, return utility for all roles

  var newstate = node.state;
  var n_iter = 0;
  while (!findterminalp(newstate, library)) {

    // for debugging simulation of games
    //if (first_loop){
    //    console.log("\nsimulating");
    //    console.log("state: " + node.state);
    //}
    if (use_heuristics && n_iter === 5) {
      break;
    }
    // random move 
    var move = seq();
    for (var i = 0; i < roles.length; i++) {
      var actions = findlegals(roles[i], newstate, library);
      move[i] = randomelement(actions);
    }

    // more debugging
    //console.log("random move: " + move);
    //console.log("new state: " + newstate);

    newstate = simulate(move, newstate, library);
    n_iter += 1;
  }

  // more debugging
  //console.log("reward: " + findreward(role,newstate,library));
  //console.log("end simulating\n");

  var reward = seq();
  for (var i = 0; i < roles.length; i++) {
    reward[i] = parseInt(findreward(roles[i], newstate, library));
    if (use_heuristics) {
      reward[i] += 0.25 * findlegals(roles[i], newstate, library).length;
    }
  }
  return reward;
}


function backpropagate(states_visited, scores) {
  for (var i = 0; i < states_visited.length; i++) {
    var node = cache[states_visited[i]];
    if (!turnbased && !is_coop) {
      node = cache[parse_state(states_visited[i])];
    }

    for (var j = 0; j < roles.length; j++) {
      node.total_utility[j] += scores[j];
    }

    node.num_visits++;
  }
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

function best_action(node, role_idx, library) {
  var actions = findlegals(roles[role_idx], node.state, library);

  if (actions.length === 1) {
    return actions[0];
  } else {



    // iterate through actions
    // var z = 0;
    var possible_moves = generate_moves(node.state, library);
    // while (z < actions.length && check_bad_state(actions[z], state, library, role) === 1) {
    //   z += 1;
    // }
    // if (z < actions.length) {
    //   action = actions[z];
    // }
    // for (var i = 0; i < actions.length; i++) {
    //   var tempscore = 0;
    //   var counter = 0;
    //   if (roles.length > 1) {
    //     const potential_bad = check_bad_state(actions[i], state, library, role);
    //     if (potential_bad === 1) {
    //       console.log("Losing action... skipping");
    //       continue;
    //     } else if (potential_bad === 2) {
    //       return actions[i];
    //     }
    //   }

    //   // create list of all possible newstates with that action
    //   var possible_moves = generate_moves(node.state, library);

    //   var action_moves = seq();
    //   for (var k = 0; k < possible_moves.length; k++) {
    //     if (JSON.stringify(possible_moves[k][role_idx]) == JSON.stringify(actions[i])) {
    //       action_moves[action_moves.length] = possible_moves[k];
    //     }
    //   }

    //   var newstates = seq();
    //   for (var k = 0; k < action_moves.length; k++) {
    //     newstates[k] = JSON.stringify(simulate(action_moves[k], node.state, library));
    //   }

    //   // check if each child state is in new states
    //   for (var j = 0; j < node.children.length; j++) {

    //     if (newstates.indexOf(JSON.stringify(node.children[j].state)) > -1 && node.children[j].num_visits > 0) {

    //       tempscore += node.children[j].total_utility[role_idx];
    //       counter += node.children[j].num_visits;
    //     }
    //   }

    //   if (counter == 0) {
    //     var newscore = 0;
    //   } else {
    //     var newscore = tempscore / counter;
    //   }
    var score = 0;
    var action = actions[0];
    for (var i = 0; i < possible_moves.length; i++) {
      // logging
      var currstate = simulate(possible_moves[i], node.state, library);
      if (!turnbased && !is_coop) {
        currstate = parse_state(currstate);
      }
      var newscore = 1.0 * cache[currstate].total_utility[role_idx] / cache[currstate].num_visits;
      console.log("action: " + possible_moves[i][role_idx] + " utility: " + cache[currstate].total_utility[role_idx] + " numvisits: " + cache[currstate].num_visits + " score: " + newscore);
      if (newscore > score) {
        score = newscore;
        action = possible_moves[i][role_idx];
      }
    }
    return action;
  }
}

function abort(id) {
  return 'done'
}

function stop(id, move) {
  return 'done'

}

//==============================================================================
// GGP basics
//==============================================================================

indexing = true;
dataindexing = false;
ruleindexing = true;

function findroles(rules) {
  return basefinds('R', seq('role', 'R'), seq(), rules)
}

function findbases(rules) {
  return basefinds('P', seq('base', 'P'), seq(), rules)
}

function findinputs(rules) {
  return basefinds('A', seq('input', 'A'), seq(), rules)
}

function findinits(rules) {
  return basefinds(seq('true', 'P'), seq('init', 'P'), seq(), rules)
}

function findlegalp(role, action, facts, rules) {
  return $legal$bb$(role, action, facts, rules)[1]
}

function findlegalx(role, facts, rules) {
  return seq('does', role, $legal$bf$(role, facts, rules))
}

function findlegals(role, facts, rules) {
  return vniquify($$legal$bf$$(role, facts, rules)).map(x => seq('does', role, x))
}

function findnexts(facts, rules) {
  return vniquify($$next$f$$(facts, rules)).map(x => seq('true', x))
}

function findterminalp(facts, rules) {
  return $terminal$$(facts, rules)
}

function findreward(role, facts, rules) {
  return $goal$bf$(role, facts, rules)
}

function simulate(move, state, rules) {
  if (move === 'nil') {
    return state
  };
  return findnexts(move.concat(state), rules)
}

//------------------------------------------------------------------------------

function doesify(roles, actions) {
  var exp = seq();
  for (var i = 0; i < roles.length; i++) {
    exp[i] = seq('does', roles[i], actions[i])
  };
  return exp
}

function undoesify(move) {
  var exp = seq();
  for (var i = 0; i < move.length; i++) {
    exp[i] = move[i][2]
  };
  return exp
}

function truify(state) {
  var exp = seq();
  for (var i = 0; i < state.length; i++) {
    exp[i] = seq('true', state[i])
  };
  return exp
}

function untruify(state) {
  var exp = seq();
  for (var i = 0; i < state.length; i++) {
    exp[i] = state[i][1]
  };
  return exp
}

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

function onRequest(request, response) {
  if (request.method === 'OPTIONS') {
    var headers = {};
    headers["Access-Control-Allow-Origin"] = "*";
    headers["Access-Control-Allow-Methods"] = "POST, GET, OPTIONS";
    headers["Access-Control-Allow-Credentials"] = false;
    headers["Access-Control-Max-Age"] = '86400';
    headers["Access-Control-Allow-Headers"] = "Sender, Receiver, Content-Type, Accept";
    response.writeHead(200, headers);
    response.end()
  } else {
    response.writeHead(200, {
      "Access-Control-Allow-Origin": "*",
      "Access-Control-Allow-Methods": "POST, GET, OPTIONS",
      "Access-Control-Allow-Headers": "*",
      "Access-Control-Allow-Age": "86400",
      "Content-Type": "text/plain"
    });
    var postData = "";
    var pathname = url.parse(request.url).pathname;
    request.setEncoding("utf8");
    request.addListener("data", function(chunk) {
      postData += chunk
    });
    request.addListener("end", function() {
      route(pathname, response, postData)
    })
  }
}

function route(pathname, response, postData) {
  var request = readkif(postData);
  console.log(printseq(request));
  var result = eval(request[0]).apply(null, request.slice(1));
  response.write(printit(result));
  console.log(printit(result));
  response.end()
}

//------------------------------------------------------------------------------

var port = (process.argv.length > 2) ? process.argv[2] : 9147;
http.createServer(onRequest).listen(port);
console.log("Server has started.");

//==============================================================================
// End
//==============================================================================