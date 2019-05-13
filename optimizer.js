//==============================================================================
// optimizer.js
//==============================================================================
//==============================================================================
// prunerules
//==============================================================================

function prunerules (rules)
 {var newrules = seq();
  for (var i=0; i<rules.length; i++)
      {if (!subsumedp(rules[i],newrules) &&
           !subsumedp(rules[i],rules.slice(i+1)))
          {newrules.push(rules[i])}};
  return newrules}

function subsumedp (rule,rules)
 {for (i=0; i<rules.length; i++)
      {if (subsumesp(rules[i],rule)) {return true}};
  return false}

function subsumesp (p,q)
 {if (equalp(p,q)) {return true};
  if (symbolp(p) || symbolp(q)) {return false};
  if (p[0]==='rule' && q[0]==='rule')
     {var al = matcher(p[1],q[1]);
      if (al!==false  && subsumesexp(p.slice(2),q.slice(2),al))
         {return true}};
  return false};

function subsumesexp (pl,ql,al)
 {if (pl.length===0) {return true};
  for (var i=0; i<ql.length; i++)
      {var bl = match(pl[0],ql[i],al);
       if (bl!==false && subsumesexp(pl.slice(1),ql,bl))
          {return true}};
  return false}

//==============================================================================
// End
//==============================================================================