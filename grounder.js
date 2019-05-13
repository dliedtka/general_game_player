//==============================================================================
// grounder.js
//==============================================================================
//==============================================================================
// grounder
//==============================================================================

function groundrules (library)
 {var facts = compfacts(library);
  var rules = seq();
  for (var i=0; i<library.length; i++)
      {rules = groundrule(library[i],facts,rules)};
  return vniquify(rules)}

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

function compfacts (library)
 {var bases = compbases(library);
  var inputs = compinputs(library);
  var tables = comptables(library);
  var facts = definemorerules(seq(),bases.concat(inputs));
  for (var i=0; i<tables.length; i++)
      {compview(tables[i],facts,library)};
  return facts}

function compbases (rules)
 {return basefinds(seq('true','P'),seq('base','P'),seq(),rules)}

function compinputs (rules)
 {return basefinds(seq('does','R','A'),seq('input','R','A'),seq(),rules).sort()}

function comptables (rules)
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
// End
//==============================================================================