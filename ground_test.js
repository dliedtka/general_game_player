//==============================================================================
// bmcsg.js
//==============================================================================
//==============================================================================
// Initialization
//==============================================================================
var http = require("http");
var url = require("url");
var querystring = require("querystring");
var fs = require('fs');
eval(fs.readFileSync('epilog.js') + '');

var matchid = '';
var role = '';
var library = [];
var startclock = 0;
var playclock = 0;

var roles = [];
var state = [];
var libraries = [];

//==============================================================================
// Player
//==============================================================================

function info ()
 {return 'ready'}

function start (id,r,rs,sc,pc)
 {matchid = id;
  library = definemorerules(seq(),rs);
  role = r;
  startclock = sc;
  playclock = pc;

  roles = findroles(library);
  state = findinits(library);
  library = definemorerules(seq(),groundrules(library));
  libraries = factors(role,library);
  for (var i=0; i<libraries.length; i++)
      {libraries[i] = definemorerules([],libraries[i])};

  console.log(role);
  console.log(state);
  console.log(findlegals(role,state,library));

  return 'ready'}

function play (id,move)
 {return playbestmcs(id,move)}
  
function abort (id)
  {return 'done'}

function stop (id,move)
  {return 'done'}

function evaluate (form)
 {return eval(stripquotes(form)).toString()}

//==============================================================================
// grounder
//==============================================================================

function groundrules (library)
 {var facts = groundfacts(library);
  var rules = seq();
  for (var i=0; i<library.length; i++)
      {rules = groundrule(library[i],facts,rules)};
  return zniquify(rules)}

function groundrule (rule,facts,rules)
 {if (symbolp(rule)) {rules[rules.length] = rule; return rules};
  if (rule[0]!=='rule') {rules[rules.length] = rule; return rules};
  return groundsubgoals(2,rule,nil,facts,rules)}

function groundsubgoals (n,rule,al,facts,rules)
 {if (n>=rule.length) {rules[rules.length] = plug(rule,al); return rules};
  if (!symbolp(rule[n]) && rule[n][0]==='distinct')
     {if (equalp(plug(rule[n][1],al),plug(rule[n][2],al))) {return rules};
      return groundsubgoals(n+1,rule,al,facts,rules)};
  if (!symbolp(rule[n]) && rule[n][0]==='not')
     {return groundsubgoals(n+1,rule,al,facts,rules)};
  var data = indexees(operator(rule[n]),facts);
  for (var i=0; i<data.length; i++)
      {var bl = match(rule[n],data[i],al);
       if (bl) {rules = groundsubgoals(n+1,rule,bl,facts,rules)}};
  return rules}

//------------------------------------------------------------------------------

function groundfacts (library)
 {var bases = groundbases(library);
  var inputs = groundinputs(library);
  var tables = gettables(library);
  var facts = definemorerules(seq(),bases.concat(inputs));
  for (var i=0; i<tables.length; i++)
      {compview(tables[i],facts,library)};
  return facts}

function groundbases (rules)
 {return basefinds(seq('true','P'),seq('base','P'),seq(),rules)}

function groundinputs (rules)
 {return basefinds(seq('does','R','A'),seq('input','R','A'),seq(),rules).sort()}

function gettables (rules)
 {return ordering(dependencies(rules))}

function dependencies (rules)
 {var ds = {};
  for (var i=0; i<rules.length; i++)
      {ds = getdependencies(rules[i],ds)};
  return ds}

function getdependencies (rule,ds)
 {if (symbolp(rule)) {return setrelation(rule,ds)};
  var rel = operator(rule);
  if (rule[0]!=='rule') {return setrelation(rel,ds)};
  for (var j=2; j<rule.length; j++) {setdepends(rel,operator(rule[j]),ds)};
  return ds}

function setrelation (r,ds)
 {var dum = ds[r];
  if (dum) {return ds};
  ds[r] = seq();
  return ds}

function setdepends (r,p,ds)
 {var dum = ds[r];
  if (dum) {return adjoin(p,dum)};
  ds[r] = seq(p);
  return ds}

function ordering (ds)
 {var rs = seq('distinct','true','does');
  var flag = true;
  while (flag)
    {flag = false;
     for (r in ds)
         {if (ds[r]!==0 && subset(ds[r],rs))
             {rs[rs.length] = r; ds[r] = 0; flag = true}}};
  return rs}

//------------------------------------------------------------------------------

function compview (r,facts,library)
 {if (r==='next') {return true};
  var data = indexees(r,library);
  for (var i=0; i<data.length; i++)
      {if (operator(data[i])===r) {comprule(data[i],facts)}};
  return true}

function comprule (rule,facts)
 {if (symbolp(rule)) {compsave(rule,facts); return true};
  if (rule[0]!=='rule') {compsave(rule,facts); return true};
  return compsubgoals(2,rule,nil,facts)}

function compsubgoals (n,rule,al,facts)
 {if (n>=rule.length) {compsave(plug(rulehead(rule),al),facts); return true};
  if (!symbolp(rule[n]) && rule[n][0]==='distinct')
     {if (!equalp(plug(rule[n][1],al),plug(rule[n][2],al)))
         {compsubgoals(n+1,rule,al,facts)};
      return true};
  if (!symbolp(rule[n]) && rule[n][0]==='not')
     {compsubgoals(n+1,rule,al,facts); return true};
  var data = indexees(operator(rule[n]),facts);
  for (var i=0; i<data.length; i++)
      {var bl = match(rule[n],data[i],al);
       if (bl) {compsubgoals(n+1,rule,bl,facts)}};
  return true}

function compsave (fact,facts)
 {var rel = operator(fact);
  if (find(fact,indexees(rel,facts))) {return fact};
  facts.push(fact);
  indexsymbol(rel,fact,facts);
  return fact}

function rulehead (p)
 {if (symbolp(p)) {return p};
  if (p[0]==='rule') {return p[1]};
  return p}

//==============================================================================
// factors
//==============================================================================

function factors (role,rules)
 {var components = newfactors(rules);
  var subgames = [];
  for (var i=0; i<components.length; i++)
      {if (wimpyp(components[i])) {continue};
       subgames.push(assemble(role,components[i],rules))};
  return subgames}

function wimpyp (factor)
 {for (var i=0; i<factor.length; i++)
      {if (symbolp(factor[i])) {continue};
       if (factor[i][0]==='does') {return false}};
  return true}

function assemble (role,component,rules)
 {var actions = getactions(role,component);
  var newrules = [];
  for (i=0; i<rules.length; i++)
      {var rule = rules[i];
       if (symbolp(rule)) {newrules.push(rule); continue};
       if (rule[0]==='legal')
          {if (find(rule[2],actions)) {newrules.push(rule)}; continue};
       if (rule[0]==='rule' && !symbolp(rule[1]) && rule[1][0]==='legal')
          {if (find(rule[1][2],actions)) {newrules.push(rule)}; continue};
       newrules.push(rule)};
  return newrules}

function splitrule (rule,component)
 {if (symbolp(rule)) {return rule};
  if (rule[0]==='rule')
     {var newrule = seq('rule',rule[1]);
      for (var i=2; i<rule.length; i++)
          {if (find(rule[i],component))
              {newrule.push(rule[i])}};
      return newrule};
  return rule}

function getactions (role,subgame)
 {var actions = [];
  for (var i=0; i<subgame.length; i++)
      {if (subgame[i][0]==='does' && subgame[i][1]===role)
          {actions.push(subgame[i][2])}};
  return actions}

//------------------------------------------------------------------------------

function compreductions (role,rules)
 {var residues = reductions('terminal',[],rules);
  var rewards = groundrewards(role,rules);
  for (var i=0; i<rewards.length; i++)
      {residues = residues.concat(reductions(rewards[i],[],rules))};
  return residues}

function groundrewards (role,rules)
 {var rewards = [];
  var data = indexees('goal',rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]==='rule'&&data[i][1][0]==='goal'&&data[i][1][1]===role)
          {rewards = adjoinit(data[i][1],rewards)};
       if (data[i][0]==='goal' && data[i][1]===role)
          {rewards = adjoinit(data[i][1],rewards)}};
  return rewards}

function reductions (goal,goals,rules)
 {var residues = [];
  reductionsexp(goal,goals,rules,['rule',goal],residues);
  return residues}

function reductionsexp (goal,goals,rules,residue,residues)
 {if (symbolp(goal))
     {return reductionsview(goal,goals,rules,residue,residues)};
  if (goal[0]==='not')
     {return reductionsexp(goal[1],goals,rules,residue,residues)};
  if (goal[0]==='and' || goal[0]==='or')
     {for (var i=1; i<goal.length; i++)
          {reductionsexp(goal[i],goals,rules,residue,residues)};
      return residues};
  if (goal[0]==='true')
     {residue = adjoin(goal,residue.slice(0));
      return reductionsexit(goals,rules,residue,residues)};
  return reductionsview(goal,goals,rules,residue,residues)}

function reductionsview (goal,goals,rules,residue,residues)
 {var data = indexees(operator(goal),rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]==='rule' && equalp(data[i][1],goal))
          {var newgoals = data[i].slice(3).concat(goals);
           reductionsexp(data[i][2],newgoals,rules,residue,residues)}};
  return residues}

function reductionsexit (goals,rules,residue,residues)
 {if (goals.length===0)
     {residues = residues.push(residue); return residues};
  return reductionsexp (goals[0],goals.slice(1),rules,residue,residues)}

//------------------------------------------------------------------------------

function newfactors (rules)
 {//var toprules = residues('robot',library)
  var bases = newbases(rules);
  var inputs = newinputs(rules);
  var factoids = bases.concat(inputs);
  var factors = [];
  for (var i=0; i<factoids.length; i++)
      {factors = addtofactors(newresidues(factoids[i],rules),factors)};
  return factors}

function newbases (rules)
 {return basefinds(seq('next','P'),seq('base','P'),seq(),rules)}

function newinputs (rules)
 {return basefinds(seq('legal','R','A'),seq('input','R','A'),seq(),rules)}

//------------------------------------------------------------------------------

function newresidues (goal,rules)
 {var newgoal = goal;
  if (!symbolp(goal) && goal[0]==='next')
     {newgoal = seq('true',goal[1])};
  if (!symbolp(goal) && goal[0]==='legal')
     {newgoal = seq('does',goal[1],goal[2])};
  return newsupports(goal,[newgoal],rules)}

function newsupports (goal,facts,rules)
 {if (symbolp(goal))
     {return newsupportsview(goal,facts,rules)};
  if (goal[0]==='not')
     {return newsupports(goal[1],facts,rules)};
  if (goal[0]==='and' || goal[0]==='or')
     {for (var i=1; i<goal.length; i++)
          {facts = newsupports(goal[i],facts,rules)};
      return facts};
  return newsupportsview(goal,facts,rules)}

function newsupportsview (goal,facts,rules)
 {if (find(goal,facts)) {return facts};
  if (!symbolp(goal) && goal[0]==='true') {facts.push(goal); return facts};
  if (!symbolp(goal) && goal[0]==='does') {facts.push(goal); return facts};
  var data = indexees(operator(goal),rules)
  for (var i=0; i<data.length; i++)
      {if (!symbolp(data[i]) && data[i][0]==='rule' && equalp(data[i][1],goal))
          {for (var j=2; j<data[i].length; j++)
               {newsupports(data[i][j],facts,rules)}}};
  return facts}

//------------------------------------------------------------------------------

function addtofactors (factor,factors)
 {var newfactor = factor;
  var newfactors = [];
  for (var i=0; i<factors.length; i++)
      {if (intersectionp(factor,factors[i]))
          {newfactor = union(factors[i],newfactor)}
       else {newfactors.push(factors[i])}};
  newfactors.push(newfactor);
  return newfactors}

function intersectionp (s1,s2)
 {for (var i=0; i<s1.length; i++)
      {if (find(s1[i],s2)) {return true}};
  return false}

function union (s1,s2)
 {var result = s1.slice(0);
  for (var i=0; i<s2.length; i++)
      {if (!find(s2[i],s1)) {result.push(s2[i])}};
  return result}

//==============================================================================
// inertiality
//==============================================================================

function inertialp (role,rules)
 {var nexts = compnexts(rules);console.log(nexts);
  for (var i=0; i<nexts.length; i++)
      {var newrules = compresidues(nexts[i],rules);console.log(newrules);
       for (var j=0; j<newrules.length; j++)
           {if (newrules[j][0]!=='rule') {break};
            if (acceptablep(newrules[j])) {continue};
            return false}};
  console.log(true);
  return true}

function acceptablep (rule)
 {var flag = false;
  for (var i=2; i<rule.length; i++)
      {if (symbolp(rule[i])) {continue};
       if (rule[i][0]==='does') {return true};
       if (rule[i][0]==='true' && equalp(rule[i][1],rule[1][1]))
          {flag = true; continue};
       if (rule[i][0]==='not') {continue};
       return false}
  return flag}

function compnexts (rules)
 {return basefinds(seq('next','P'),seq('base','P'),seq(),rules)}

//------------------------------------------------------------------------------

function compresidues (goal,rules)
 {var newgoals = [];
  var newrules = [];
  groundsupports(goal,[],rules,newgoals,newrules);
  return newrules}

function groundsupports (goal,facts,rules,newgoals,newrules)
 {if (symbolp(goal))
     {return groundsupportsview(goal,facts,rules,newgoals,newrules)};
  if (goal[0]==='not')
     {return groundsupports(goal[1],facts,rules,newgoals,newrules)};
  if (goal[0]==='and' || goal[0]==='or')
     {for (var i=1; i<goal.length; i++)
          {groundsupports(goal[i],facts,rules,newgoals,newrules)};
      return newrules};
  if (find(goal,facts)) {return newrules};
  return groundsupportsview(goal,facts,rules,newgoals,newrules)}

function groundsupportsview (goal,facts,rules,newgoals,newrules)
 {if (find(goal,newgoals)) {return newrules};
  newgoals.push(goal);
  var data = indexees(operator(goal),rules)
  for (var i=0; i<data.length; i++)
      {if (equalp(data[i],goal))
          {newrules.push(data[i])};
       if (!symbolp(data[i]) && data[i][0]==='rule' && equalp(data[i][1],goal))
          {newrules.push(data[i]);
           for (var j=2; j<data[i].length; j++)
               {groundsupports(data[i][j],facts,rules,newgoals,newrules)}}};
  return newrules}

//==============================================================================
// bestmcs
//==============================================================================

function playbestmcs (id,move)
 {if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
  var action = 'noop';
  var score = -1;
  var deadline = Date.now();
  var increment = (playclock-4)*1000/libraries.length;
  for (var i=0; i<libraries.length; i++)
      {deadline = deadline+increment;
       var answer = bestmcs_bestmove(role,state,libraries[i],deadline);
       if (answer[0]>score) {score = answer[0]; action=answer[1]};
       if (score===100) {return action[2]}};
  return action[2]}

function bestmcs_bestmove (role,state,library,deadline)
 {var actions = findlegals(role,state,library);
  var scores = seq();
  if (actions.length===0) {return [0,['does',role,'noop']]};
  //if (actions.length===1) {return [0,actions[0]]};
  for (var i=0; i<actions.length; i++) {scores[i] = 0};
  var action = actions[0];
  var score = 0;
  var i = 0;
  var probes = 0
  while (Date.now()<deadline)
   {if (i>=actions.length) {i = 0};
    var result = depthchargeothers(role,actions[i],0,seq(),state,library);
    scores[i] = scores[i] + result;
    if (scores[i]>score) {score = scores[i]; action = actions[i]};
    probes++;
    i++};
  //console.log(probes);
  //console.log(score);
  return [score,action]}

//------------------------------------------------------------------------------

function depthcharge (role,state,library)
 {if (findterminalp(state,library))
     {return findreward(role,state,library)*1};
  var move = seq();
  for (var i=0; i<roles.length; i++)
      {var options = findlegals(roles[i],state,library);
       if (options.length===0) {return 0};
       var best = randomindex(options.length);
       move[i] = options[best]};
  var newstate = simulate(move,state,library);
  return depthcharge(role,newstate,library)}

function depthchargeothers (role,action,rn,move,state,library)
 {if (rn>=roles.length)
     {var newstate = simulate(move,state,library);
      return depthcharge(role,newstate,library)};
  if (roles[rn]==role)
     {move[rn] = action;
      return depthchargeothers(role,action,rn+1,move,state,library)};
  var actions = findlegals(roles[rn],state,library);
  var score = 100;
  for (var i=0; i<actions.length; i++)
      {move[rn] = actions[i];
       var result = depthchargeothers(role,action,rn+1,move,state,library);
       if (result==0) {return 0};
       if (result<score) {score = result}};
  return score}

//------------------------------------------------------------------------------
// random
//------------------------------------------------------------------------------

function playrandom (id,move)
 {if (move!=='nil') {state = simulate(doesify(roles,move),state,library)};
  var actions=findlegals(role,state,library);
  var ind = randomindex(actions.length);
  return actions[ind][2]}

function randomindex (n)
 {return Math.floor(Math.random()*n)}

//==============================================================================
// GGP basics
//==============================================================================

function findroles (rules)
 {return basefinds('R',seq('role','R'),seq(),rules)}

function findbases (rules)
 {return basefinds('P',seq('base','P'),seq(),rules)}

function findinputs (role,rules)
 {return basefinds('A',seq('input',role,'A'),seq(),rules)}

function findinits (rules)
 {return basefinds(seq('true','P'),seq('init','P'),seq(),rules)}

function findlegalp (role,ply,facts,rules)
 {return groundfindp(seq('legal',role,ply),facts,rules)}

function findlegalx (role,facts,rules)
 {return groundvalue('legal',role,facts,rules)}

function findlegals (role,facts,rules)
 {return groundvalues('legal',role,facts,rules).map(x => ['does',role,x])}

function findnexts (facts,rules)
 {return truify(grounditems('next',facts,rules)).sort()}

function findreward (role,facts,rules)
 {var value = groundvalue('goal',role,facts,rules);
  if (value) {return value};
  return 0}

function findterminalp (facts,rules)
 {return groundfindp('terminal',facts,rules)}

//------------------------------------------------------------------------------

function simulate (move,state,rules)
 {return findnexts(move.concat(state),rules)}

function doesify (roles,actions)
 {var exp = [];
  for (var i=0; i<roles.length; i++)
      {exp[i] = seq('does',roles[i],actions[i])};
  return exp}

function undoesify (move)
 {var exp = [];
  for (var i=0; i<move.length; i++)
      {exp[i] = move[i][2]};
  return exp}

function truify (state)
 {var exp = [];
  for (var i=0; i<state.length; i++)
      {exp[i] = seq('true',state[i])};
  return exp}

function untruify (state)
 {var exp = [];
  for (var i=0; i<state.length; i++)
      {exp[i] = state[i][1]};
  return exp}

//------------------------------------------------------------------------------
// groundfindp
//------------------------------------------------------------------------------

function groundfindp (p,facts,rules)
 {inferences = inferences + 1;
  if (symbolp(p)) {return groundfindatom(p,facts,rules)};
  if (p[0]==='same') {return equalp(p[1],p[2])};
  if (p[0]==='distinct') {return !equalp(p[1],p[2])};
  if (p[0]==='not') {return !groundfindp(p[1],facts,rules)};
  if (groundfindbackground(p,facts,rules)) {return true};
  return groundfindrs(p,facts,rules)}

function groundcompute (rel,facts,rules)
 {var answers = seq();
  var data = facts;
  for (var i=0; i<data.length; i++)
      {if (operator(data[i])===rel) {answers.push(data[i])}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {if (equalp(data[i],rel)) {answers.push(rel)}}
       else if (data[i][0]!=='rule')
               {if (equalp(operator(data[i]),rel)) {answers.push(data[i])}}
       else {if (equalp(operator(data[i]),rel) &&
                 groundfindsubs(data[i],facts,rules))
                {answers.push(data[i][1])}}};
  return uniquify(answers)}

function groundfindatom (p,facts,rules)
 {if (p==='true') {return true};
  if (p==='false') {return false};
  if (groundfindbackground(p,facts,rules)) {return true};
  return groundfindrs(p,facts,rules)}

function groundfindbackground (p,facts,rules)
 {//var data = factindexps(p,facts);
  data = facts;
  for (var i=0; i<data.length; i++)
      {if (equalp(data[i],p)) {return true}};
  return false}

function groundfindrs (p,facts,rules)
 {var data = viewindexps(p,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {if (equalp(data[i],p)) {return true}}
       else if (data[i][0]!=='rule') {if (equalp(data[i],p)) {return true}}
       else {if (equalp(data[i][1],p) && groundfindsubs(data[i],facts,rules))
                {return true}}};
  return false}

function groundfindsubs (rule,facts,rules)
 {for (var j=2; j<rule.length; j++)
      {if (!groundfindp(rule[j],facts,rules)) {return false}};
  return true}

function factindexps (p,theory)
 {if (symbolp(p)) {return indexees(p,theory)};
  var best = indexees(p[0],theory);
  for (var i=1; i<p.length; i++)
      {var dum = factindexps(p[i],theory);
       if (dum.length<best.length) {best = dum}};
  return best}

function grounditems (rel,facts,rules)
 {var answers=seq();
  var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel)
               {answers.push(data[i][1])}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel)
                   {answers.push(data[i][1])}}
       else {var head=data[i][1];
             if (operator(head)===rel &&
                 groundfindsubs(data[i],facts,rules))
                {answers.push(head[1])}}};
  return uniquify(answers)}

function groundvalue (rel,obj,facts,rules)
 {var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel && data[i][1]===obj) {return data[i][2]}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel && data[i][1]===obj) {return data[i][2]}}
       else {var head=data[i][1];
             if (operator(head)===rel && equalp(head[1],obj) &&
                 groundfindsubs(data[i],facts,rules))
                {return data[i][1][2]}}};
  return false}

function groundvalues (rel,obj,facts,rules)
 {var answers=seq();
  var data = facts;
  for (var i=0; i<data.length; i++) {
    console.log(data[i]);
    console.log(rel);
    console.log(obj);
    if (symbolp(data[i])) {
        continue
      } else if (data[i][0]===rel && data[i][1]===obj) {
        answers.push(data[i][2]);
      }
    };
  console.log(answers);
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel && data[i][1]===obj)
                   {answers.push(data[i][2])}}
       else {var head=data[i][1];
             if (operator(head)===rel && equalp(head[1],obj) &&
                 groundfindsubs(data[i],facts,rules))
                {answers.push(head[2])}}};
  return uniquify(answers)}

//==============================================================================
// Epilog parameters
//==============================================================================

indexing = true;
dataindexing = false;
ruleindexing = true;

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

var port = (process.argv.length > 2) ? process.argv[2] : 9146;
http.createServer(onRequest).listen(port);
console.log("Server has started.");

//==============================================================================
// End
//==============================================================================