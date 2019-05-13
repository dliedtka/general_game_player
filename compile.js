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
 {return basefinds('P',seq('init','P'),seq(),rules)}

function findlegalp (role,action,facts,rules)
 {return $legal$bb$(role,action,facts,rules)[1]}

function findlegalx (role,facts,rules)
 {return seq('does',role,$legal$bf$(role,facts,rules))}

function findlegals (role,facts,rules)
 {return vniquify($$legal$bf$$(role,facts,rules)).map(x => seq('does',role,x))}

function findnexts (facts,rules)
 {return vniquify($$next$$(facts,rules)).map(x => seq('true',x[1]))}

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
// End
//==============================================================================