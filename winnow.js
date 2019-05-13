//==============================================================================
// winnow.js
//==============================================================================

function winnow (role,rules)
 {var rewards = groundrewards(role,rules);
  var newgoals = [];
  var newrules = [];
  groundsupports('terminal',rules,newgoals,newrules);
  for (var i=0; i<rewards.length; i++)
      {groundsupports(rewards[i],rules,newgoals,newrules)};
  return newrules}

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

function groundsupports (goal,rules,newgoals,newrules)
 {if (symbolp(goal))
     {return groundsupportsview(goal,rules,newgoals,newrules)};
  if (goal[0]==='not')
     {return groundsupports(goal[1],rules,newgoals,newrules)};
  if (goal[0]==='and' || goal[0]==='or')
     {for (var i=1; i<goal.length; i++)
          {groundsupports(goal[i],rules,newgoals,newrules)};
      return newrules};
  if (goal[0]==='true')
     {groundsupports(seq('next',goal[1]),rules,newgoals,newrules)};
  if (goal[0]==='does')
     {groundsupports(seq('legal',goal[1],goal[2]),rules,newgoals,newrules)};
  return groundsupportsview(goal,rules,newgoals,newrules)}

function groundsupportsview (goal,rules,newgoals,newrules)
 {if (find(goal,newgoals)) {return newrules};
  newgoals.push(goal);
  var data = indexees(operator(goal),rules)
  for (var i=0; i<data.length; i++)
      {if (equalp(data[i],goal))
          {newrules.push(data[i])};
       if (!symbolp(data[i]) && data[i][0]==='rule' && equalp(data[i][1],goal))
          {newrules.push(data[i]);
           for (var j=2; j<data[i].length; j++)
               {groundsupports(data[i][j],rules,newgoals,newrules)}}};
  return newrules}

//==============================================================================
// End
//==============================================================================