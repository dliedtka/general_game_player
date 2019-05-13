//==============================================================================
// compiler.js
//==============================================================================
//==============================================================================
// overall
//==============================================================================

function compile (rules)
 {var code = '';
  code += prettycompile(rules);
  code += prettyprogram(rules);
  return code}

//==============================================================================
// normalize
//==============================================================================

function normalize (rules)
 {var out = [];
  for (var i=0; i<rules.length; i++)
      {out.push(normalizerule(rules[i]))};
  return out}

function normalizerule (rule)
 {if (symbolp(rule)) {return seq('rule',rule,true)};
  if (rule[0]==='transition') {return rule};
  if (rule[0]==='definition') {return rule};
  var newrule= seq('rule',rule[1]);
  for (var i=2; i<rule.length; i++)
      {newrule.push(normalizesubgoal(rule[i]))};
  return newrule}

function normalizesubgoal (subgoal)
 {if (symbolp(subgoal)) {return subgoal};
  if (subgoal[0]==='matches')
     {var query = seq('matches',subgoal[1],subgoal[2]);
      var result = seq('cons',newvar(),listify(subgoal.slice(3)));
      return seq('evaluate',query,result)};
  if (subgoal[0]==='submatches')
     {var query = seq('submatches',subgoal[1],subgoal[2]);
      var result = seq('cons',subgoal[3],newvar());
      return seq('evaluate',query,result)};
  if (builtinp(subgoal[0]))
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  if (mathp(subgoal[0]))
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  if (listop(subgoal[0]))
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  if (subgoal[0]==='map')
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  if (subgoal[0]==='setofall')
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  if (subgoal[0]==='countofall')
     {return seq('evaluate',subgoal.slice(0,-1),subgoal[subgoal.length-1])};
  return subgoal}

//==============================================================================
// compile
//==============================================================================
//------------------------------------------------------------------------------
// prettycompile
//------------------------------------------------------------------------------

function prettycompile (rules)
 {var code = '';
  var views = getviewsfromrules(rules);
  for (var i=0; i<views.length; i++)
      {code += prettyjs(compileoneview(views[i],rules));
       code += prettyjs(compileallview(views[i],rules))};
  var atoms = getatomsfromrules(rules);
  for (var i=0; i<atoms.length; i++)
      {code += prettyjs(compileoneatomlist(atoms[i],rules));
       code += prettyjs(compileallatomlist(atoms[i],rules))};
  var bases = getbasesfromrules(rules);
  for (var i=0; i<bases.length; i++)
      {code += prettyjs(compileonebase(bases[i]));
       code += prettyjs(compileallbase(bases[i]))};
  return code}

//------------------------------------------------------------------------------
// compileoneview
//------------------------------------------------------------------------------

function compileoneview (view,rules)
 {var data = indexees(view,rules);
  var code = seq('function',single(view),seq('query','al','facts','rules'));
  code.push(seq('bind','answer','false'));
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       code.push(compileoneviewrule(rule))};
  code.push(seq('return','answer'));
  return code}

function compileoneviewrule (rule)
 {var hlist = vars(rule[1]);
  var blist = {};
  var code = seq('block');
  code.push(seq('bind','head',codify(rule[1],[],{})));
  for (var i=2; i<rule.length; i++)
      {code.push(seq('bind','sub'+(i-1),codify(rule[i],[],{})))};
  code.push(seq('bind','bl',seq('obj')));
  code.push(seq('bind','ol',seq('seq')));
  var cond = seq('vnify','query','al','head','bl','ol');
  var subcode = seq('block');
  subcode.push(compileoneviewsubgoals(rule,2,hlist,blist));
  subcode.push(seq('backup','ol'));
  code.push(seq('if',cond,subcode));
  return code};

function compileoneviewsubgoals (rule,n,hlist,blist)
 {if (n>=rule.length)
     {var result = codify(rule[1],hlist,blist);
      return seq('block',seq('bind','answer',result))};
  return compileoneviewsubgoal(rule,n,hlist,blist)}

function compileoneviewsubgoal (rule,n,hlist,alist)
 {if (symbolp(rule[n]))
     {return compileoneviewatom(rule,n,hlist,alist)};
  if (rule[n][0]==='same')
     {return compileoneviewsame(rule,n,hlist,alist)};
  if (rule[n][0]==='distinct')
     {return compileoneviewdistinct(rule,n,hlist,alist)};
  if (rule[n][0]==='evaluate')
     {return compileoneviewevaluate(rule,n,hlist,alist)};
  if (rule[n][0]==='true' && rule[n].length===3)
     {return compileoneviewtrue(rule,n,hlist,alist)};
  if (rule[n][0]==='not')
     {return compileoneviewnot(rule,n,hlist,alist)};
  if (compgroundp(rule[n],alist))
     {return compileoneviewbound(rule,n,hlist,alist)};
  if (n===rule.length-1)
     {return compileoneviewlast(rule,n,hlist,alist)};
  return compileoneviewdb(rule,n,hlist,alist)}

function compileoneviewatom (rule,n,hlist,alist)
 {if (rule[n]==='true') {return compileoneviewsubgoals(rule,n+1,hlist,alist)};
  if (rule[n]==='false') {return 'false'};
  var subroutine = single(rule[n]);
  var cond = seq(subroutine,kwotify(rule[n]),'bl','facts','rules');
  return seq('if',cond,compileoneviewsubgoals(rule,n+1,hlist,alist))}

function compileoneviewsame (rule,n,hlist,alist)
 {var x = codify(rule[n][1],hlist,alist);
  var y = codify(rule[n][2],hlist,alist);
  var cond = seq('equalp',x,y);
  var code = compileoneviewsubgoals(rule,n+1,hlist,alist);
  return seq('if',cond,code)}

function compileoneviewdistinct (rule,n,hlist,alist)
 {var x = codify(rule[n][1],hlist,alist);
  var y = codify(rule[n][2],hlist,alist);
  var cond = seq('equalp',x,y);
  var code = compileoneviewsubgoals(rule,n+1,hlist,alist);
  return seq('if',seq('not',cond),code)}

function compileoneviewevaluate (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var subgoal = seq('companswerx',subvar,'bl','facts','rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n],datavar,hlist,alist,'ol');
  block.push(seq('if',datavar,compileoneviewsubgoals(rule,n+1,hlist,alist)));
  return block}

function compileoneviewtrue (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var olvar = 'ol'+(n-1);
  var source = seq('sub','datasets',kwotify(rule[n][2]));
  var subgoal = seq(plural(operator(rule[n][1])),seq('sub',subvar,'1'),'bl',source,'rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n][1],seq('sub',datavar,indvar),hlist,alist,olvar);
  var bind = seq('maatchify',seq('sub',subvar,'1'),'bl',seq('sub',datavar,indvar),'bl',olvar);
  var code = compileoneviewsubgoals(rule,n+1,hlist,alist);
  var inner = seq('block');
  inner.push(seq('bind',olvar,seq('seq')));
  inner.push(bind);
  inner.push(code);
  inner.push(seq('backup',olvar));
  block.push(seq('loop',indvar,'0',datavar+'.length',inner));
  return block}

function compileoneviewnot (rule,n,hlist,blist)
 {var cond = compilecall(rule[n][1],hlist,blist); 
  var code = compileoneviewsubgoals(rule,n+1,hlist,blist);
  return seq('if',seq('not',cond),code)}

function compileoneviewbound (rule,n,hlist,alist)
 {var subroutine = single(operator(rule[n]));
  var cond = seq(subroutine,codify(rule[n],hlist,alist),'bl','facts','rules');
  return seq('if',cond,compileoneviewsubgoals(rule,n+1,hlist,alist))}

function compileoneviewlast (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var subgoal = seq(single(operator(rule[n])),subvar,'bl','facts','rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n],datavar,hlist,alist,'ol');
  block.push(seq('if',datavar,compileoneviewsubgoals(rule,n+1,hlist,alist)));
  return block}

function compileoneviewdb (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var olvar = 'ol'+(n-1);
  var subgoal = seq(plural(operator(rule[n])),subvar,'bl','facts','rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n],seq('sub',datavar,indvar),hlist,alist,olvar);
  var bind = seq('maatchify',subvar,'bl',seq('sub',datavar,indvar),'bl',olvar);
  var code = compileoneviewsubgoals(rule,n+1,hlist,alist);
  var inner = seq('block');
  inner.push(seq('bind',olvar,seq('seq')));
  inner.push(bind);
  inner.push(code);
  inner.push(seq('backup',olvar));
  inner.push(seq('if','answer','break'));
  block.push(seq('loop',indvar,'0',datavar+'.length',inner));
  return block}

//------------------------------------------------------------------------------
// compileoneatomlist
//------------------------------------------------------------------------------

function compileoneatomlist (view,rules)
 {var name = single(view);
  var params = ['query','al','facts','rules'];
  var dataname = static(view);
  var code = ['baseanswerx','query','al',dataname];
  return seq('function',name,params,seq('return',code))}

//------------------------------------------------------------------------------
// compileonebase
//------------------------------------------------------------------------------

function compileonebase (rel)
 {var params = ['query','al','facts','rules'];
  return seq('function',single(rel),params,
             seq('return',seq('dataanswerx').concat(params)))}

//------------------------------------------------------------------------------
// compileallview
//------------------------------------------------------------------------------

function compileallview (view,rules)
 {var data = indexees(view,rules);
  var code = seq('function',plural(view),seq('query','al','facts','rules'));
  code.push(seq('bind','answers',seq('seq')));
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       code.push(compileallviewrule(rule))};
  code.push(seq('return','answers'));
  return code}

function compileallviewrule (rule)
 {var hlist = vars(rule[1]);
  var blist = {};
  var code = seq('block');
  code.push(seq('bind','head',codify(rule[1],[],{})));
  for (var i=2; i<rule.length; i++)
      {code.push(seq('bind','sub'+(i-1),codify(rule[i],[],{})))};
  code.push(seq('bind','bl',seq('obj')));
  code.push(seq('bind','ol',seq('seq')));
  var cond = seq('vnify','query','al','head','bl','ol');
  var subcode = seq('block');
  subcode.push(compileallviewsubgoals(rule,2,hlist,blist));
  subcode.push(seq('backup','ol'));
  code.push(seq('if',cond,subcode));
  return code};

function compileallviewsubgoals (rule,n,hlist,blist)
 {if (n>=rule.length)
     {var result = codify(rule[1],hlist,blist);
      return seq('block',seq('answers.push',result))};
  return compileallviewsubgoal(rule,n,hlist,blist)}

function compileallviewsubgoal (rule,n,hlist,alist)
 {if (symbolp(rule[n]))
     {return compileallviewatom(rule,n,hlist,alist)};
  if (rule[n][0]==='same')
     {return compileallviewsame(rule,n,hlist,alist)};
  if (rule[n][0]==='distinct')
     {return compileallviewdistinct(rule,n,hlist,alist)};
  if (rule[n][0]==='evaluate')
     {return compileallviewevaluate(rule,n,hlist,alist)};
  if (rule[n][0]==='true' && rule[n].length===3)
     {return compileallviewtrue(rule,n,hlist,alist)};
  if (rule[n][0]==='not')
     {return compileallviewnot(rule,n,hlist,alist)};
  if (compgroundp(rule[n],alist))
     {return compileallviewbound(rule,n,hlist,alist)};
  return compileallviewdb(rule,n,hlist,alist)}

function compileallviewatom (rule,n,hlist,alist)
 {if (rule[n]==='true') {return compileallviewsubgoals(rule,n+1,hlist,alist)};
  if (rule[n]==='false') {return 'false'};
  var subroutine = single(rule[n]);
  var cond = seq(subroutine,kwotify(rule[n]),'bl','facts','rules');
  return seq('if',cond,compileallviewsubgoals(rule,n+1,hlist,alist))}

function compileallviewsame (rule,n,hlist,alist)
 {var x = codify(rule[n][1],hlist,alist);
  var y = codify(rule[n][2],hlist,alist);
  var cond = seq('equalp',x,y);
  var code = compileallviewsubgoals(rule,n+1,hlist,alist);
  return seq('if',cond,code)}

function compileallviewdistinct (rule,n,hlist,alist)
 {var x = codify(rule[n][1],hlist,alist);
  var y = codify(rule[n][2],hlist,alist);
  var cond = seq('equalp',x,y);
  var code = compileallviewsubgoals(rule,n+1,hlist,alist);
  return seq('if',seq('not',cond),code)}

function compileallviewevaluate (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var subgoal = seq('companswerx',subvar,'bl','facts','rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n],datavar,hlist,alist,'ol');
  block.push(seq('if',datavar,compileallviewsubgoals(rule,n+1,hlist,alist)));
  return block}

function compileallviewtrue (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var olvar = 'ol'+(n-1);
  var source = seq('sub','datasets',kwotify(rule[n][2]));
  var subgoal = seq(plural(operator(rule[n][1])),seq('sub',subvar,'1'),'bl',source,'rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n][1],seq('sub',datavar,indvar),hlist,alist,olvar);
  var bind = seq('maatchify',seq('sub',subvar,'1'),'bl',seq('sub',datavar,indvar),'bl',olvar);
  var code = compileallviewsubgoals(rule,n+1,hlist,alist);
  var inner = seq('block');
  inner.push(seq('bind',olvar,seq('seq')));
  inner.push(bind);
  inner.push(code);
  inner.push(seq('backup',olvar));
  block.push(seq('loop',indvar,'0',datavar+'.length',inner));
  return block}

function compileallviewnot (rule,n,hlist,blist)
 {var cond = compilecall(rule[n][1],hlist,blist);
  var code = compileallviewsubgoals(rule,n+1,hlist,blist);
  return seq('if',seq('not',cond),code)}

function compileallviewbound (rule,n,hlist,alist)
 {var subroutine = single(operator(rule[n]));
  var cond = seq(subroutine,codify(rule[n],hlist,alist),'bl','facts','rules');
  return seq('if',cond,compileallviewsubgoals(rule,n+1,hlist,alist))}

function compileallviewdb (rule,n,hlist,alist)
 {var subvar = 'sub'+(n-1);
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var olvar = 'ol'+(n-1);
  var subgoal = seq(plural(operator(rule[n])),subvar,'bl','facts','rules');
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  compilematch(rule[n],seq('sub',datavar,indvar),hlist,alist,olvar);
  var bind = seq('maatchify',subvar,'bl',seq('sub',datavar,indvar),'bl',olvar);
  var code = compileallviewsubgoals(rule,n+1,hlist,alist);
  var inner = seq('block');
  inner.push(seq('bind',olvar,seq('seq')));
  inner.push(bind);
  inner.push(code);
  inner.push(seq('backup',olvar));
  block.push(seq('loop',indvar,'0',datavar+'.length',inner));
  return block}

//------------------------------------------------------------------------------

function compilecall (subgoal,hlist,blist)
 {if (symbolp(subgoal))
     {return compilecallatom(subgoal,hlist,blist)};
  if (subgoal[0]==='same')
     {return compilecallsame(subgoal,hlist,blist)};
  if (subgoal[0]==='distinct')
     {return compilecalldistinct(subgoal,hlist,blist)};
  if (subgoal[0]==='evaluate')
     {return compilecallevaluate(subgoal,hlist,blist)};
  if (subgoal[0]==='true' && subgoal.length===3)
     {return compilecalltrue(subgoal,hlist,blist)};
  return compilecalldb(subgoal,hlist,blist)}

function compilecallatom (subgoal,hlist,blist)
 {return seq('$' + subgoal + '$',seq('seq'),'facts','rules')}

function compilecallsame (subgoal,hlist,blist)
 {var x1 = codify(subgoal[1],[],blist);
  var x2 = codify(subgoal[2],[],blist);
  return seq('equalp',x1,x2)}

function compilecalldistinct (subgoal,hlist,blist)
 {var x1 = codify(subgoal[1],[],blist);
  var x2 = codify(subgoal[2],[],blist);
  return seq('not',seq('equalp',x1,x2))}

function compilecallevaluate (subgoal,hlist,blist)
 {var query = codify(subgoal,hlist,blist);
  return seq('companswerx',query,'bl','facts','rules')}

function compilecalltrue (subgoal,hlist,blist)
 {var source = seq('sub','datasets',kwotify(subgoal[2]));
  var subroutine = single(operator(subgoal[1]));
  var query = codify(subgoal[1],hlist,blist);
  return seq(subroutine,query,seq('seq'),source,'rules')}

function compilecalldb (subgoal,hlist,blist)
 {var subroutine = single(operator(subgoal));
  var query = codify(subgoal,hlist,blist);
  return seq(subroutine,query,seq('seq'),'facts','rules')}

//------------------------------------------------------------------------------

function compilecalls (subgoal,hlist,blist)
 {if (symbolp(subgoal))
     {return compilecallsdb(subgoal,hlist,blist)};
  if (subgoal[0]==='true' && subgoal.length===3)
     {return compilecallstrue(subgoal,hlist,blist)};
  return compilecallsdb(subgoal,hlist,blist)}

function compilecallstrue (subgoal,hlist,blist)
 {var source = seq('sub','datasets',kwotify(subgoal[2]));
  var subroutine = plural(operator(subgoal[1]));
  var query = codify(subgoal[1],hlist,blist);
  return seq(subroutine,query,seq('seq'),source,'rules')}

function compilecallsdb (subgoal,hlist,blist)
 {var subroutine = plural(operator(subgoal));
  var query = codify(subgoal,hlist,blist);
  return seq(subroutine,query,seq('seq'),'facts','rules')}

//------------------------------------------------------------------------------
// compileallatomlist
//------------------------------------------------------------------------------

function compileallatomlist (view,rules)
 {var name = plural(view);
  var params = ['query','al','facts','rules'];
  var dataname = static(view);
  var code = ['baseanswers','query','al',dataname];
  return seq('function',name,params,seq('return',code))}

//------------------------------------------------------------------------------
// compileallbase
//------------------------------------------------------------------------------

function compileallbase (rel)
 {var params = ['query','al','facts','rules'];
  return seq('function',plural(rel),params,
             seq('return',seq('dataanswers').concat(params)))}

//==============================================================================
// program
//==============================================================================
//------------------------------------------------------------------------------
// prettyprogram
//------------------------------------------------------------------------------

function prettyprogram (rules)
 {var code = '';
  var views = getviewsfromrules(rules);
  for (var i=0; i<views.length; i++)
      {var arity = getarity(views[i],rules);
       if (arity===0)
          {code += prettyjs(programoneviewbound(views[i],rules))};
       if (arity===1)
          {code += prettyjs(programoneviewbound(views[i],rules));
           code += prettyjs(programoneviewf(views[i],rules));
           code += prettyjs(programallviewf(views[i],rules))};
       if (arity===2)
          {code += prettyjs(programoneviewbound(views[i],rules));
           code += prettyjs(programoneviewbf(views[i],rules));
           code += prettyjs(programoneviewfb(views[i],rules));
           code += prettyjs(programoneviewfree(views[i],rules));
           code += prettyjs(programallviewbf(views[i],rules));
           code += prettyjs(programallviewfb(views[i],rules));
           code += prettyjs(programallviewfree(views[i],rules))};
       if (arity>2)
          {code += prettyjs(programoneviewbound(views[i],rules));
           code += prettyjs(programoneviewfree(views[i],rules));
           code += prettyjs(programallviewfree(views[i],rules))}};
  var atoms = getatomsfromrules(rules);
  for (var i=0; i<atoms.length; i++)
      {var arity = getarity(atoms[i],rules);
       if (arity===0)
          {code += prettyjs(programoneatombound(atoms[i],rules))};
       if (arity===1)
          {code += prettyjs(programoneatombound(atoms[i],rules))
           code += prettyjs(programoneatomf(atoms[i],rules));
           code += prettyjs(programallatomf(atoms[i],rules))};
       if (arity===2)
          {code += prettyjs(programoneatombound(atoms[i],rules))
           code += prettyjs(programoneatombf(atoms[i],rules));
           code += prettyjs(programoneatomfb(atoms[i],rules));
           code += prettyjs(programoneatomfree(atoms[i],rules));
           code += prettyjs(programallatombf(atoms[i],rules));
           code += prettyjs(programallatomfb(atoms[i],rules));
           code += prettyjs(programallatomfree(atoms[i],rules))};
       if (arity>2)
          {code += prettyjs(programoneatombound(atoms[i],rules));
           code += prettyjs(programoneatomfree(atoms[i],rules));
           code += prettyjs(programallatomfree(atoms[i],rules))};
       code += prettyjs(programatomdata(atoms[i],rules))};
  var bases = getbasesfromrules(rules);
  for (var i=0; i<bases.length; i++)
      {var arity = getarity(bases[i],rules);
       if (arity===0)
          {code += prettyjs(programonebasebound(bases[i],rules))};
       if (arity===1)
          {code += prettyjs(programonebasebound(bases[i],rules));
           code += prettyjs(programonebasef(bases[i],rules));
           code += prettyjs(programallbasef(bases[i],rules))};
       if (arity===2)
          {code += prettyjs(programonebasebound(bases[i],rules));
           code += prettyjs(programonebasebf(bases[i],rules));
           code += prettyjs(programonebasefb(bases[i],rules));
           code += prettyjs(programonebasefree(bases[i],rules));
           code += prettyjs(programallbasebf(bases[i],rules));
           code += prettyjs(programallbasefb(bases[i],rules));
           code += prettyjs(programallbasefree(bases[i],rules))};
       if (arity===3)
          {code += prettyjs(programonebasebound(bases[i],rules));
           code += prettyjs(programonebasefree(bases[i],rules));
           code += prettyjs(programallbaseffb(bases[i],rules));
           code += prettyjs(programallbasefree(bases[i],rules))};
       if (arity>3)
          {code += prettyjs(programonebasebound(bases[i],rules));
           code += prettyjs(programonebasefree(bases[i],rules));
           code += prettyjs(programallbasefree(bases[i],rules))}};
  return code}

//------------------------------------------------------------------------------
// programoneview cases
//------------------------------------------------------------------------------

function programoneviewbound (view,rules)
 {var arity = getrulearity(view,rules);
  var dataset = static(view);
  var subroutine = specialn(view,arity);
  var params = [];
  for (var i=0; i<arity; i++) {params.push('x' + (i+1))};
  params.push('facts');
  params.push('rules');
  var code = seq('function',subroutine,params);
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       var cond = [];
       for (var j=0; j<params.length-2; j++)
           {cond.push(skinnymatch(params[j],rule[1][j+1],blist))};
       cond = programands(cond);
       var subcode = programoneviewsubgoals(rule,2,blist,true);
       code.push(seq('if',cond,subcode))};
  code.push(seq('return','false'));
  return code}

function programoneviewf (view,rules)
 {var subroutine = special(view,'f');
  var code = seq('function',subroutine,seq('facts','rules'));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       code.push(programoneviewsubgoals(rule,2,blist,rule[1][1]))};
  code.push(seq('return','false'));
  return code}

function programoneviewbf (view,rules)
 {var subroutine = special(view,'bf');
  var code = seq('function',subroutine,seq('x1','facts','rules'));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       var cond = skinnymatch('x1',rule[1][1],blist);
       var subcode = programoneviewsubgoals(rule,2,blist,rule[1][2]);
       code.push(seq('if',cond,subcode))};
  code.push(seq('return','false'));
  return code}

function programoneviewfb (view,rules)
 {var subroutine = special(view,'fb');
  var code = seq('function',subroutine,seq('x2','facts','rules'));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       var cond = skinnymatch('x2',rule[1][2],blist);
       var subcode = programoneviewsubgoals(rule,2,blist,rule[1][1]);
       code.push(seq('if',cond,subcode))};
  code.push(seq('return','false'));
  return code}

function programoneviewfree (view,rules)
 {var arity = getrulearity(view,rules);
  var subroutine = special(view,makesequence('f',arity));
  var code = seq('function',subroutine,seq('facts','rules'));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       code.push(programoneviewsubgoals(rule,2,blist,rule[1]))};
  code.push(seq('return','false'));
  return code}

function programoneviewsubgoals (rule,n,blist,out)
 {if (n>=rule.length)
     {if (typeof(out)==='boolean') {return seq('return','true')};
      return seq('return',codify(out,[],blist))};
  return programoneviewsubgoal(rule,n,blist,out)}

function programoneviewsubgoal (rule,n,blist,out)
 {if (symbolp(rule[n]))
     {return programoneviewsubatom(rule,n,blist,out)};
  if (rule[n][0]==='same')
     {return programoneviewsubsame(rule,n,blist,out)};
  if (rule[n][0]==='distinct')
     {return programoneviewsubdistinct(rule,n,blist,out)};
  if (rule[n][0]==='evaluate')
     {return programoneviewsubevaluate(rule,n,blist,out)};
  if (rule[n][0]==='true' && rule[n].length===3)
     {return programoneviewsubtrue(rule,n,blist,out)};
  if (rule[n][0]==='not')
     {return programoneviewsubnot(rule,n,blist,out)};
  if (compgroundp(rule[n],blist))
     {return programoneviewsubbound(rule,n,blist,out)};
  if (rule[n].length-1===1 && compfp(rule[n],blist))
     {return programoneviewsubf(rule,n,blist,out)};
  if (rule[n].length-1===2 && compbfp(rule[n],blist))
     {return programoneviewsubbf(rule,n,blist,out)};
  if (rule[n].length-1===2 && compfbp(rule[n],blist))
     {return programoneviewsubfb(rule,n,blist,out)};
  if (rule[n].length-1===3 && compffbp(rule[n],blist))
     {return programoneviewsubffb(rule,n,blist,out)};
  if (compfreep(rule[n],blist))
     {return programoneviewsubfree(rule,n,blist,out)};
  if (n===rule.length-1)
     {return programoneviewsublast(rule,n,blist,out)};
  return programoneviewsubdb(rule,n,blist,out)}

function programoneviewsubatom (rule,n,blist,out)
 {if (rule[n]==='true') {return programoneviewsubgoals(rule,n+1,blist,out)};
  if (rule[n]==='false') {return 'false'};
  var subroutine = single(rule[n]);
  var cond = seq(subroutine,'facts','rules');
  return seq('if',cond,programoneviewsubgoals(rule,n+1,blist,out))}

function programoneviewsubsame (rule,n,blist,out)
 {var x = codify(rule[n][1],[],blist);
  var y = codify(rule[n][2],[],blist);
  var cond = seq('equalp',x,y);
  var code = programoneviewsubgoals(rule,n+1,blist,out);
  return seq('if',cond,code)}

function programoneviewsubdistinct (rule,n,blist,out)
 {var x = codify(rule[n][1],[],blist);
  var y = codify(rule[n][2],[],blist);
  var cond = seq('equalp',x,y);
  var code = programoneviewsubgoals(rule,n+1,blist,out);
  return seq('if',seq('not',cond),code)}

function programoneviewsubevaluate (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var query = codify(rule[n][1],[],blist);
  var subgoal = seq('compvalue',query,'facts','rules')
  var cond = skinnymatch(datavar,rule[n][2],blist);
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('if',cond,programoneviewsubgoals(rule,n+1,blist,out)));
  return block}

function programoneviewsubtrue (rule,n,blist,out)
 {var source = seq('sub','datasets',kwotify(rule[n][2]));
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subgoal = compilecalls(rule[n],[],blist);
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsubnot (rule,n,blist,out)
 {var cond = programcall(rule[n][1],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out);
  return seq('if',seq('not',cond),code)}

function programoneviewsubbound (rule,n,blist,out)
 {var subroutine = specialn(operator(rule[n]),rule[n].length-1);
  var cond = seq(subroutine);
  for (var i=1; i<rule[n].length; i++)
      {cond.push(skinnyplug(rule[n][i],blist))}
  cond.push('facts');
  cond.push('rules');
  return seq('if',cond,programoneviewsubgoals(rule,n+1,blist,out))}

function programoneviewsubf (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'f');
  var subcode = seq(subroutine,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsubbf (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'bf');
  var query = codify(rule[n][1],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][2],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsubfb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'fb');
  var query = codify(rule[n][2],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsubffb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'ffb');
  var query = codify(rule[n][3],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsubfree (rule,n,blist,out)
 {var arity = rule[n].length-1;
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),makesequence('f',arity));
  var subcode = seq(subroutine,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programoneviewsublast (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var subgoal = compilecall(rule[n],[],blist);
  skinnymatch(datavar,rule[n],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('if',datavar,code));
  return block}

function programoneviewsubdb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subgoal = compilecalls(rule[n],[],blist);
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programoneviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

//------------------------------------------------------------------------------

function programcall (subgoal,blist)
 {if (symbolp(subgoal))
     {return programcallatom(subgoal,blist)};
  if (subgoal[0]==='same')
     {return programcallsame(subgoal,blist)};
  if (subgoal[0]==='distinct')
     {return programcalldistinct(subgoal,blist)};
  if (subgoal[0]==='evaluate')
     {return programcallevaluate(subgoal,blist)};
  if (subgoal[0]==='true' && subgoal.length===3)
     {return programcalltrue(subgoal,blist)};
  if (compgroundp(subgoal,blist))
     {return programcallbound(subgoal,blist)};
  if (subgoal.length-1===1 && compfp(subgoal,blist))
     {return programcallf(subgoal,blist)};
  if (subgoal.length-1===2 && compbfp(subgoal,blist))
     {return programcallbf(subgoal,blist)};
  if (subgoal.length-1===2 && compfbp(subgoal,blist))
     {return programcallfb(subgoal,blist)};
  if (subgoal.length-1===3 && compffbp(subgoal,blist))
     {return programcallffb(subgoal,blist)};
  if (compfreep(subgoal,blist))
     {return programcallfree(subgoal,blist)};
  return programcalldb(subgoal,blist)}

function programcallatom (subgoal,blist)
 {return seq('$' + subgoal + '$$','facts','rules')}

function programcallsame (subgoal,blist)
 {var x1 = codify(subgoal[1],[],blist);
  var x2 = codify(subgoal[2],[],blist);
  return seq('equalp',x1,x2)}

function programcalldistinct (subgoal,blist)
 {var x1 = codify(subgoal[1],[],blist);
  var x2 = codify(subgoal[2],[],blist);
  return seq('not',seq('equalp',x1,x2))}

function programcallevaluate (subgoal,blist)
 {var query = codify(subgoal,[],blist);
  return seq('companswerx',query,'bl','facts','rules')}

function programcalltrue (subgoal,blist)
 {var source = seq('sub','datasets',kwotify(subgoal[2]));
  var subroutine = single(operator(subgoal[1]));
  var query = codify(subgoal[1],[],blist);
  return seq(subroutine,query,seq('seq'),source,'rules')}

function programcallbound (subgoal,blist)
 {var arity = subgoal.length-1;
  var subroutine = special(operator(subgoal),makesequence('b',arity));
  var code = [subroutine];
  for (var i=1; i<subgoal.length; i++)
      {code.push(codify(subgoal[i],[],blist))}
  code.push('facts');
  code.push('rules');
  return code}

function programcallf (subgoal,blist)
 {var subroutine = '$' + operator(subgoal) + '$f$';
  return seq(subroutine,'facts','rules')}

function programcallbf (subgoal,blist)
 {var subroutine = '$' + operator(subgoal) + '$bf$';
  var query = codify(subgoal[1],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallfb (subgoal,blist)
 {var subroutine = '$' + operator(subgoal) + '$fb$';
  var query = codify(subgoal[2],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallffb (subgoal,blist)
 {var subroutine = '$' + operator(subgoal) + '$ffb$';
  var query = codify(subgoal[3],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallfree (subgoal,blist)
 {var arity = subgoal.length-1;
  var subroutine = special(operator(subgoal),makesequence('f',arity))
  var code = [subroutine];
  for (var i=1; i<subgoal.length; i++)
      {code.push(codify(subgoal[i],[],blist))}
  code.push('facts');
  code.push('rules');
  return code}

function programcalldb (subgoal,blist)
 {var subroutine = single(operator(subgoal));
  var query = codify(subgoal,[],blist);
  return seq(subroutine,query,seq('seq'),'facts','rules')}

//------------------------------------------------------------------------------
// programoneatom cases
//------------------------------------------------------------------------------

function programoneatombound (rel,rules)
 {var arity = getfactarity(rel,rules);
  var dataset = static(rel);
  var subroutine = '$' + rel + '$' + makesequence('b',arity) + '$';
  var params = [];
  for (var i=0; i<arity; i++) {params.push('x' + (i+1))};
  var code = seq('block');
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  for (var i=0; i<arity; i++)
      {code.push(seq('bind','dum',seq('baseindexps',params[i],dataset)));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))))};
  var cond = [];
  for (var i=0; i<arity; i++)
      {cond.push(seq('equalp',seq('sub',seq('sub','data','i'),i+1),params[i]))};
  cond = programands(cond);
  var inner = seq('if',cond,seq('return','true'));
  code.push(seq('loop','i','0','data.length',inner));
  code.push(seq('return','false'));
  return seq('function',subroutine,params,code)}

//------------------------------------------------------------------------------

function programoneatomf (rel,rules)
 {var dataset = static(rel);
  var subroutine = special(rel,'f');
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  var cond = seq('greater','data.length','0');
  code.push(seq('if',cond,seq('return',seq('sub',seq('sub','data','0'),'1'))));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programoneatombf (rel,rules)
 {var dataset = static(rel);
  var subroutine = special(rel,'bf');
  var params = seq('x1','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  code.push(seq('bind','dum',seq('baseindexps','x1',dataset)));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =  seq('equalp',seq('sub',seq('sub','data','i'),'1'),'x1');
  var result = seq('sub',seq('sub','data','i'),'2');
  var subcode = seq('if',cond,seq('return',result));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programoneatomfb (rel,rules)
 {var dataset = static(rel);
  var subroutine = special(rel,'fb');
  var params = seq('x2','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  code.push(seq('bind','dum',seq('baseindexps','x2','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  var cond =  seq('equalp',seq('sub',seq('sub','data','i'),'2'),'x2');
  var result = seq('sub',seq('sub','data','i'),'1');
  var subcode = seq('if',cond,seq('return',result));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programoneatomfree (rel,rules)
 {var arity = getrulearity(rel,rules);
  var dataset = static(rel);
  var subroutine = special(rel,makesequence('f',arity));
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  var cond = seq('greater','data.length','0');
  code.push(seq('if',cond,seq('return',seq('sub','data','0'))));
  code.push(seq('return','false'))
  return code}

//------------------------------------------------------------------------------
// programonebase cases
//------------------------------------------------------------------------------

function programonebasebound (rel,rules)
 {var arity = getarity(rel,rules);
  var subroutine = '$' + rel + '$' + makesequence('b',arity) + '$';
  var params = [];
  for (var i=0; i<arity; i++) {params.push('x' + (i+1))};
  params.push('facts');
  var code = seq('block');
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  for (var i=0; i<arity; i++)
      {code.push(seq('bind','dum',seq('fullindexps',params[i],'facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))))};
  var cond = [seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel))];
  for (var i=0; i<arity; i++)
      {cond.push(seq('equalp',seq('sub',seq('sub','data','i'),i+1),params[i]))};
  cond = programands(cond);
  var inner = seq('if',cond,seq('return','true'));
  code.push(seq('loop','i','0','data.length',inner));
  code.push(seq('return','false'));
  return seq('function',subroutine,params,code)}

//------------------------------------------------------------------------------

function programonebasef (rel,rules)
 {var subroutine = special(rel,'f');
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  var cond = seq('greater','data.length','0');
  code.push(seq('if',cond,seq('return',seq('sub',seq('sub','data','0'),'1'))));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programonebasebf (rel,rules)
 {var subroutine = special(rel,'bf');
  var params = seq('x1','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  code.push(seq('bind','dum',seq('fullindexps','x1','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =
    seq('and',
        seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel)),
        seq('equalp',seq('sub',seq('sub','data','i'),1),'x1'));
  var result = seq('sub',seq('sub','data','i'),2);
  var subcode = seq('if',cond,seq('return',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programonebasefb (rel,rules)
 {var subroutine = special(rel,'fb');
  var params = seq('x2','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  code.push(seq('bind','dum',seq('fullindexps','x2','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond = 
    seq('and',
        seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel)),
        seq('equalp',seq('sub',seq('sub','data','i'),2),'x2'));
  var result = seq('sub',seq('sub','data','i'),1);
  var subcode = seq('if',cond,seq('return',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','false'));
  return code}

//------------------------------------------------------------------------------

function programonebasefree (rel,rules)
 {var arity = getarity(rel,rules);
  var subroutine = special(rel,makesequence('f',arity));
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  var cond = seq('greater','data.length','0');
  code.push(seq('if',cond,seq('return',seq('sub','data','0'))));
  code.push(seq('return','false'))
  return code}

//------------------------------------------------------------------------------
// programallview cases
//------------------------------------------------------------------------------

function programallviewf (view,rules)
 {var subroutine = specials(view,'f');
  var code = seq('function',subroutine,seq('facts','rules'));
  code.push(seq('bind','answers',seq('seq')));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       code.push(programallviewsubgoals(rule,2,blist,1))};
  code.push(seq('return','answers'));
  return code}

function programallviewbf (view,rules)
 {var subroutine = specials(view,'bf');
  var code = seq('function',subroutine,seq('x1','facts','rules'));
  code.push(seq('bind','answers',seq('seq')));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       var cond = skinnymatch('x1',rule[1][1],blist);
       code.push(seq('if',cond,programallviewsubgoals(rule,2,blist,2)))};
  code.push(seq('return','answers'));
  return code}

function programallviewfb (view,rules)
 {var subroutine = specials(view,'fb');
  var code = seq('function',subroutine,seq('x2','facts','rules'));
  code.push(seq('bind','answers',seq('seq')));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       var cond = skinnymatch('x2',rule[1][2],blist);
       code.push(seq('if',cond,programallviewsubgoals(rule,2,blist,1)))};
  code.push(seq('return','answers'));
  return code}

function programallviewfree (view,rules)
 {var arity = getrulearity(view,rules);
  var subroutine = specials(view,makesequence('f',arity));
  var code = seq('function',subroutine,seq('facts','rules'));
  code.push(seq('bind','answers',seq('seq')));
  var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {var rule = data[i];
       if (atomp(rule)) {rule = seq('rule',rule,'true')};
       var blist = {};
       code.push(programallviewsubgoals(rule,2,blist,rule[1]))};
  code.push(seq('return','answers'));
  return code}

function programallviewsubgoals (rule,n,blist,out)
 {if (n>=rule.length)
     {if (typeof(out)==='number') {var result = codify(rule[1][out],[],blist)}
         else {var result = codify(out,[],blist)};
      return seq('answers.push',result)};
  return programallviewsubgoal(rule,n,blist,out)}

function programallviewsubgoal (rule,n,blist,out)
 {if (symbolp(rule[n]))
     {return programallviewsubatom(rule,n,blist,out)};
  if (rule[n][0]==='same')
     {return programallviewsubsame(rule,n,blist,out)};
  if (rule[n][0]==='distinct')
     {return programallviewsubdistinct(rule,n,blist,out)};
  if (rule[n][0]==='evaluate')
     {return programallviewsubevaluate(rule,n,blist,out)};
  if (rule[n][0]==='true' && rule[n].length===3)
     {return programallviewsubtrue(rule,n,blist,out)};
  if (rule[n][0]==='not')
     {return programallviewsubnot(rule,n,blist,out)};
  if (compgroundp(rule[n],blist))
     {return programallviewsubbound(rule,n,blist,out)};
  if (rule[n].length-1===1 && compfp(rule[n],blist))
     {return programallviewsubf(rule,n,blist,out)};
  if (rule[n].length-1===2 && compbfp(rule[n],blist))
     {return programallviewsubbf(rule,n,blist,out)};
  if (rule[n].length-1===2 && compfbp(rule[n],blist))
     {return programallviewsubfb(rule,n,blist,out)};
  if (rule[n].length-1===3 && compffbp(rule[n],blist))
     {return programallviewsubffb(rule,n,blist,out)};
  if (compfreep(rule[n],blist))
     {return programallviewsubfree(rule,n,blist,out)};
  return programallviewsubdb(rule,n,blist,out)}

function programallviewsubatom (rule,n,blist,out)
 {if (rule[n]==='true') {return programallviewsubgoals(rule,n+1,blist,out)};
  if (rule[n]==='false') {return 'false'};
  var subroutine = single(rule[n]);
  var cond = seq(subroutine,'facts','rules');
  return seq('if',cond,programallviewsubgoals(rule,n+1,blist,out))}

function programallviewsubsame (rule,n,blist,out)
 {var x = codify(rule[n][1],[],blist);
  var y = codify(rule[n][2],[],blist);
  var cond = seq('equalp',x,y);
  var code = programallviewsubgoals(rule,n+1,blist,out);
  return seq('if',cond,code)}

function programallviewsubdistinct (rule,n,blist,out)
 {var x = codify(rule[n][1],[],blist);
  var y = codify(rule[n][2],[],blist);
  var cond = seq('equalp',x,y);
  var code = programallviewsubgoals(rule,n+1,blist,out);
  return seq('if',seq('not',cond),code)}

function programallviewsubevaluate (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var query = codify(rule[n][1],[],blist);
  var subgoal = seq('compvalue',query,'facts','rules')
  var cond = skinnymatch(datavar,rule[n][2],blist);
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('if',cond,programallviewsubgoals(rule,n+1,blist,out)));
  return block}

function programallviewsubtrue (rule,n,blist,out)
 {var source = seq('sub','datasets',kwotify(rule[n][2]));
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subgoal = compilecalls(rule[n],[],blist);
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubnot (rule,n,blist,out)
 {var cond = programcall(rule[n][1],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out);
  return seq('if',seq('not',cond),code)}

function programallviewsubbound (rule,n,blist,out)
 {var subroutine = specialn(operator(rule[n]),rule[n].length-1);
  var cond = seq(subroutine);
  for (var i=1; i<rule[n].length; i++)
      {cond.push(skinnyplug(rule[n][i],blist))}
  cond.push('facts');
  cond.push('rules');
  return seq('if',cond,programallviewsubgoals(rule,n+1,blist,out))}

function programallviewsubf (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'f');
  var subcode = seq(subroutine,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubbf (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'bf');
  var query = codify(rule[n][1],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][2],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubfb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'fb');
  var query = codify(rule[n][2],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n][1],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubffb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),'ffb');
  var query = codify(rule[n][3],[],blist);
  var subcode = seq(subroutine,query,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubfree (rule,n,blist,out)
 {var arity = rule[n].length-1;
  var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subroutine = specials(operator(rule[n]),makesequence('f',arity));
  var subcode = seq(subroutine,'facts','rules');
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subcode));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

function programallviewsubdb (rule,n,blist,out)
 {var datavar = 'l'+(n-1);
  var indvar = 'i'+(n-1);
  var subgoal = compilecalls(rule[n],[],blist);
  skinnymatch(seq('sub',datavar,indvar),rule[n],blist);
  var code = programallviewsubgoals(rule,n+1,blist,out)
  var block = seq('block');
  block.push(seq('bind',datavar,subgoal));
  block.push(seq('loop',indvar,'0',datavar+'.length',code));
  return block}

//------------------------------------------------------------------------------

function programcalls (subgoal,blist)
 {if (symbolp(subgoal)) {return programcallatom(subgoal,blist)};
  if (compgroundp(subgoal,blist)) {return programcallsbound(subgoal,blist)};
  var subroutine = plural(operator(subgoal));
  var query = codify(subgoal,[],blist);
  return seq(subroutine,query,seq('seq'),'facts','rules')}

function programcallsatom (subgoal,blist)
 {return seq('$' + subgoal + '$$','facts','rules')}

function programcallsbound (subgoal,blist)
 {var subroutine = specialn(subgoal[0],subgoal.length-1);
  var code = [subroutine];
  for (var i=1; i<subgoal.length; i++)
      {code.push(codify(subgoal[i],blist))}
  code.push('facts');
  code.push('rules');
  return code}

function programcallsbf (subgoal,blist)
 {var subroutine = '$$' + operator(subgoal) + '$bf$$';
  var query = codify(subgoal[1],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallsfb (subgoal,blist)
 {var subroutine = '$$' + operator(subgoal) + '$fb$$';
  var query = codify(subgoal[2],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallsffb (subgoal,blist)
 {var subroutine = '$$' + operator(subgoal) + '$ffb$$';
  var query = codify(subgoal[3],[],blist);
  return seq(subroutine,query,'facts','rules')}

function programcallsff (subgoal,blist)
 {var subroutine = '$$' + operator(subgoal) + '$ff$$';
  return seq(subroutine,'facts','rules')}

//------------------------------------------------------------------------------
// programallatomlist cases
//------------------------------------------------------------------------------

function programallatomf (rel,rules)
 {var dataset = static(rel);
  var subroutine = specials(rel,'f');
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  var method = seq('dot',seq('indexees',kwotify(rel),dataset),'map');
  //var arg = seq('transform','x',seq('sub','x','1'));
  var arg = 'arg1';
  code.push(seq('return',seq('method',method,arg)));
  return code}

//------------------------------------------------------------------------------

function programallatombf (rel,rules)
 {var dataset = static(rel);
  var subroutine = specials(rel,'bf');
  var params = seq('x1','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  code.push(seq('bind','dum',seq('baseindexps','x1',dataset)));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =  seq('equalp',seq('sub',seq('sub','data','i'),'1'),'x1');
  var result = seq('sub',seq('sub','data','i'),'2');
  var subcode = seq('if',cond,seq('answers.push',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','answers'));
  return code}

//------------------------------------------------------------------------------

function programallatomfb (rel,rules)
 {var dataset = static(rel);
  var subroutine = specials(rel,'fb');
  var params = seq('x2','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('baseindexees',kwotify(rel),dataset)));
  code.push(seq('bind','dum',seq('baseindexps','x2',dataset)));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =  seq('equalp',seq('sub',seq('sub','data','i'),'2'),'x2');
  var result = seq('sub',seq('sub','data','i'),'1');
  var subcode = seq('if',cond,seq('answers.push',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','answers'));
  return code}

//------------------------------------------------------------------------------

function programallatomfree (rel,rules)
 {var arity = getrulearity(rel,rules);
  var dataset = static(rel);
  var subroutine = specials(rel,makesequence('f',arity));
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('return',seq('baseindexees',kwotify(rel),dataset)));
  return code}

//------------------------------------------------------------------------------
// programallbase cases
//------------------------------------------------------------------------------

function programallbasef (rel,rules)
 {var subroutine = specials(rel,'f');
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  var method = seq('dot',seq('indexees',kwotify(rel),'facts'),'map');
  //var arg = seq('transform','x',seq('sub','x','1'));
  var arg = 'arg1';
  code.push(seq('return',seq('method',method,arg)));
  return code}

//------------------------------------------------------------------------------

function programallbasebf (rel,rules)
 {var subroutine = specials(rel,'bf');
  var params = seq('x1','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  code.push(seq('bind','dum',seq('fullindexps','x1','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =
    seq('and',
        seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel)),
        seq('equalp',seq('sub',seq('sub','data','i'),1),'x1'));
  var result = seq('sub',seq('sub','data','i'),2);
  var subcode = seq('if',cond,seq('answers.push',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','answers'));
  return code}

//------------------------------------------------------------------------------

function programallbasefb (rel,rules)
 {var subroutine = specials(rel,'fb');
  var params = seq('x2','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  code.push(seq('bind','dum',seq('fullindexps','x2','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =
    seq('and',
        seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel)),
        seq('equalp',seq('sub',seq('sub','data','i'),2),'x2'));
  var result = seq('sub',seq('sub','data','i'),1);
  var subcode = seq('if',cond,seq('answers.push',result));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','answers'));
  return code}

//------------------------------------------------------------------------------

function programallbaseffb (rel,rules)
 {var subroutine = specials(rel,'ffb');
  var params = seq('x3','facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('bind','data',seq('indexees',kwotify(rel),'facts')));
  code.push(seq('bind','dum',seq('fullindexps','x3','facts')));
  var cond = seq('and','dum',seq('less','dum.length','data.length'));
  code.push(seq('if',cond,seq('block',seq('bind','data','dum'))));
  var cond =
    seq('and',
        seq('eq',seq('sub',seq('sub','data','i'),0),kwotify(rel)),
        seq('equalp',seq('sub',seq('sub','data','i'),3),'x3'));
  var subcode = seq('if',cond,seq('answers.push',seq('sub','data','i')));
  code.push(seq('bind','answers',seq('seq')));
  code.push(seq('loop','i','0','data.length',subcode));
  code.push(seq('return','answers'));
  return code}

//------------------------------------------------------------------------------

function programallbasefree (rel,rules)
 {var arity = getarity(rel,rules);
  var subroutine = specials(rel,makesequence('f',arity));
  var params = seq('facts','rules');
  var code = seq('function',subroutine,params);
  code.push(seq('return',seq('indexees',kwotify(rel),'facts')));
  return code}

//------------------------------------------------------------------------------
// programatomdata
//------------------------------------------------------------------------------

function programatomdata (view,rules)
 {var data = indexees(view,rules);
  var name = static(view);
  var code = ['defineindex',['readdata','`' + grindem(data) + '`']];
  return seq('bind',name,code)}

//==============================================================================
// Miscellaneous
//==============================================================================
//------------------------------------------------------------------------------
// getmyviews
// getviewsfromrules
// getatomsfromrules
// getbasesfromrules
//------------------------------------------------------------------------------

function getmyviews (data)
 {var views = seq();
  for (var i=0; i<data.length; i++)
      {var datum =  data[i];
       if (datum==='true' || datum==='false') {continue};
       if (symbolp(datum)) {adjoin(datum,views); continue};
       if (datum[0]==='definition') {continue};
       if (datum[0]==='transition') {continue};
       if (datum[0]==='rule') {adjoin(operator(datum),views); continue};
       adjoin(datum[0],views)};
  return views}

//------------------------------------------------------------------------------

function getviewsfromrules (rules)
 {var views = getmyviews(rules);
  var tables = seq();
  for (var i=0; i<views.length; i++)
      {if (!atomlistp(views[i],rules)) {tables = adjoin(views[i],tables)}};
  return tables}

//------------------------------------------------------------------------------

function getatomsfromrules (rules)
 {var views = getmyviews(rules);
  var tables = seq();
  for (var i=0; i<views.length; i++)
      {if (views[i]==='definition') {continue};
       if (views[i]==='transition') {continue};
       if (atomlistp(views[i],rules)) {tables = adjoin(views[i],tables)}};
  return tables}

function atomlistp (view,rules)
 {var data = indexees(view,rules);
  for (var i=0; i<data.length; i++)
      {if (!atomp(data[i])) {return false}};
  return true}

function atomp (rule)
 {return (symbolp(rule) || rule[0]!=='rule')};

//------------------------------------------------------------------------------

function getbasesfromrules (rules)
 {var bases = seq();
  var views = getmyviews(rules);
  for (var i=0; i<rules.length; i++)
      {bases = getbasesexp(rules[i],views,bases)};
  return bases}

function getbasesexp (rule,views,bases)
 {if (symbolp(rule))
     {if (!find(rule,views)) {return adjoin(rule,bases)};
      return bases};
  if (rule[0]==='same') {return bases};
  if (rule[0]==='distinct') {return bases};
  if (rule[0]==='evaluate') {return bases};
  if (rule[0]==='true' && rule.length===3) {return bases};
  if (rule[0]==='not') {return getbasesexp(rule[1],views,bases)};
  if (rule[0]==='and' || rule[0]==='or')
     {for (var i=1; i<rule.length; i++)
          {bases = getbasesexp(rule[i],views,bases)};
      return bases};
  if (rule[0]==='definition') {return bases};
  if (rule[0]==='rule')
     {for (var i=2; i<rule.length; i++)
          {bases = getbasesexp(rule[i],views,bases)};
      return bases};
  if (rule[0]==='transition') {return bases};
  if (find(rule[0],views)) {return bases};
  return adjoin(rule[0],bases)}

function basep (rel,rules)
 {return (indexees(rel,rules).length===0)}

//------------------------------------------------------------------------------
// compilegroundp
// compilealmostp
//------------------------------------------------------------------------------

function compgroundp (x,blist)
 {if (varp(x)) {return blist[x]!==undefined};
  if (symbolp(x)) {return true};
  for (var i=1; i<x.length; i++)
      {if (!compgroundp(x[i],blist)) {return false}};
  return true}

function compfp (subgoal,blist)
 {if (!varp(subgoal[1])) {return false};
  if (blist[subgoal[1]]!==undefined) {return false};
  return true}

function compbfp (subgoal,blist)
 {if (!compgroundp(subgoal[1],blist)) {return false};
  if (!varp(subgoal[2])) {return false};
  if (blist[subgoal[2]]!==undefined) {return false};
  return true}

function compfbp (subgoal,blist)
 {if (!varp(subgoal[1])) {return false};
  if (blist[subgoal[1]]!==undefined) {return false};
  if (!compgroundp(subgoal[2],blist)) {return false};
  return true}

function compffbp (subgoal,blist)
 {if (!varp(subgoal[1])) {return false};
  if (blist[subgoal[1]]!==undefined) {return false};
  if (!varp(subgoal[2])) {return false};
  if (blist[subgoal[2]]!==undefined) {return false};
  if (!compgroundp(subgoal[3],blist)) {return false};
  return true}

function compfreep (subgoal,blist)
 {for (var i=1; i<subgoal.length; i++)
      {if (!varp(subgoal[i])) {return false};
       if (blist[subgoal[i]]!==undefined) {return false};
       if (subgoal.indexOf(subgoal[i],i+1)>0) {return false}};
  return true}

//------------------------------------------------------------------------------
// compilematch
//------------------------------------------------------------------------------

function compilematch (x,y,hlist,alist,ol)
 {if (varp(x))
     {if (alist[x]) {return seq('equalp',alist[x],y)};
      if (find(x,hlist))
         {alist[x] = y;;
          return seq('maatchify',kwotify(x),'bl',y,'bl',ol)};
      alist[x] = y;
      return 'true'};
  if (symbolp(x)) {return seq('eq',kwotify(x),y)};
  var code = [];
  for (var i=0; i<x.length; i++)
      {code.push(compilematch(x[i],seq('sub',y,i),hlist,alist,ol))};
  code = programands(code);
  return code}

//------------------------------------------------------------------------------
// skinnymatch
//------------------------------------------------------------------------------

function skinnymatch (x,y,blist)
 {if (varp(y))
     {if (blist[y]!==undefined) {return seq('equalp',blist[y],x)};
      blist[y] = x;
      return 'true'};
  if (symbolp(y)) {return seq('eq',x,kwotify(y))};
  var cond = seq(seq('not',seq('symbolp',x)));
  for (var i=0; i<y.length; i++)
      {cond.push(skinnymatch(seq('sub',x,i),y[i],blist))};
  return programands(cond)}

function skinnyplug (x,blist)
 {if (varp(x))
     {if (blist[x]) {return blist[x]};
      return kwotify(x)};
  if (symbolp(x)) {return kwotify(x)};
  var exp = seq('seq');
  for (var i=0; i<x.length; i++)
      {exp.push(skinnyplug(x[i],blist))};
  return exp}

//------------------------------------------------------------------------------
// sundry
//------------------------------------------------------------------------------

function single (s)
 {return '$' + s + '$'}

function plural (s)
 {return '$$' + s + '$$'}

function static (s)
 {return '$' + s + '$data$'}

function special (rel,suffix)
 {return '$' + rel + '$' + suffix + '$'}

function specials (rel,suffix)
 {return '$$' + rel + '$' + suffix + '$$'}

function specialn (rel,n)
 {var out = '$' + rel + '$';
  for (var i=0; i<n; i++) {out += 'b'};
  out += '$'; 
  return out}

function codify (x,hlist,alist)
 {if (varp(x))
     {if (alist[x]) {return alist[x]};
      if (find(x,hlist)) {return seq('pluug',kwotify(x),'bl','bl')};
      return kwotify(x)};
  if (symbolp(x)) {return kwotify(x)};
  var exp = seq('seq');
  for (var i=0; i<x.length; i++)
      {exp.push(codify(x[i],hlist,alist))};
  return exp}

function kwotify (x)
 {return ("'" + x + "'")}

function makesequence (char,n)
 {var out = '';
  for (var i=0; i<n; i++)
      {out = out.concat([char])};
  return out}

function getarity (rel,rules)
 {for (var i=0; i<rules.length; i++)
      {var dum = getarityexp(rel,rules[i]);
       if (dum) {return dum}};
  return 0}

function getarityexp (rel,x)
 {if (symbolp(x)) {if (x===rel) {return 0} else {return false}};
  if (x[0]===rel) {return x.length-1};
  for (var i=1; i<x.length; i++)
      {var dum = getarityexp(rel,x[i]);
       if (dum) {return dum}};
  return false}

function programands (s)
 {if (s.length===0) {return 'true'};
  if (s.length===1) {return s[0]};
  var out = ['and'];
  for (var i=0; i<s.length; i++)
      {if (s[i]==='true') {continue};
       if (s[i]==='false') {return 'false'};
       out.push(s[i])};
  if (out.length===1) {return 'true'};
  if (out.length===2) {return out[1]};
  return out}

//==============================================================================
// grind
//==============================================================================
//------------------------------------------------------------------------------
// prettyjs
//------------------------------------------------------------------------------

function prettyjs (x)
 {return '\r' + prettifyjs(x,0) + '\r'}

function prettifyjs (x,n)
 {if (symbolp(x)) {return x};
  if (x[0]==='seq') {return '[' + grindjsargs(x.slice(1)) + ']'};
  if (x[0]==='obj') {return '{' + grindjsargs(x.slice(1)) + '}'};
  if (x[0]==='dot') {return grindjs(x[1]) + '.' + grindjs(x[2])};
  if (x[0]==='sub') {return grindjs(x[1]) + '[' + x[2] + ']'};
  if (x[0]==='bind') {return "var " + x[1] + " = " + grindjs(x[2])};
  if (x[0]==='method') {return grindjs(x[1]) + grindjsarglist(x.slice(2))};
  if (x[0]==='transform') {return grindjs(x[1]) + ' => ' + grindjs(x[2])};
  if (x[0]==='less') {return grindjs(x[1]) + '<' + grindjs(x[2])};
  if (x[0]==='greater') {return grindjs(x[1]) + '>' + grindjs(x[2])};
  if (x[0]==='eq') {return grindjs(x[1]) + '===' + grindjs(x[2])};
  if (x[0]==='if')
     {var answer = 'if (' + grindjs(x[1]) + ")\r";
      answer += grindindent(n+3) + prettifyjs(x[2],n+3);
      return answer};
  if (x[0]==='not') {return "!" + grindjs(x[1])};
  if (x[0]==='and')
     {var answer = '(';
      for (var i=1; i<x.length-1; i++)
          {answer += grindjs(x[i]) + ' && '};
      answer += grindjs(x[x.length-1]) + ')';
      return answer};
  if (x[0]==='return') {return "return " + grindjs(x[1])};
  if (x[0]==='block')
     {var answer = '{';
      if (x.length>1) {answer += prettifyjs(x[1],n+1) + ';'};
      for (var i=2; i<x.length; i++)
          {answer += '\r' + grindindent(n+1) + prettifyjs(x[i],n+1) + ';'};
      answer += '}';
      return answer};
  if (x[0]==='loop')
     {var answer = 'for ';
      answer += '(var ' + x[1] + '=' + x[2] + '; ';
      answer += x[1] + '<' + x[3] + '; ';
      answer += x[1] + '++)\r';
      answer += grindindent(n+4) + prettifyjs(x[4],n+4);
      return answer}
  if (x[0]=== 'function')
     {var answer = 'function ' + x[1] + ' ' + grindjsarglist(x[2]) + '\r';
      answer += grindindent(n+1) + '{';
      if (x.length>3) {answer += prettifyjs(x[3],n+2)};
      for (var i=4; i<x.length; i++)
          {answer += ';\r' + grindindent(n+2) + prettifyjs(x[i],n+2)};
      answer += '}';
      return answer}
  return x[0] + grindjsarglist(x.slice(1))}

//------------------------------------------------------------------------------
// grindjs
//------------------------------------------------------------------------------

function grindjs (x)
 {if (symbolp(x)) {return x};
  if (x[0]==='seq') {return '[' + grindjsargs(x.slice(1)) + ']'};
  if (x[0]==='obj') {return '{' + grindjsargs(x.slice(1)) + '}'};
  if (x[0]==='dot') {return grindjs(x[1]) + '.' + grindjs(x[2])};
  if (x[0]==='sub') {return grindjs(x[1]) + '[' + x[2] + ']'};
  if (x[0]==='bind') {return "var " + x[1] + " = " + grindjs(x[2])};
  if (x[0]==='method') {return grindjs(x[1]) + grindjsarglist(x.slice(2))};
  if (x[0]==='transform') {return grindjs(x[1]) + ' => ' + grindjs(x[2])};
  if (x[0]==='less') {return grindjs(x[1]) + '<' + grindjs(x[2])};
  if (x[0]==='greater') {return grindjs(x[1]) + '>' + grindjs(x[2])};
  if (x[0]==='eq') {return grindjs(x[1]) + '===' + grindjs(x[2])};
  if (x[0]==='if') {return "if (" + grindjs(x[1]) + ")\r" + grindjs(x[2])};
  if (x[0]==='not') {return "!" + grindjs(x[1])};
  if (x[0]==='and')
     {var answer = '';
      for (var i=1; i<x.length-1; i++)
          {answer += grindjs(x[i]) + ' && '};
      answer += grindjs(x[x.length-1]);
      return answer};
  if (x[0]==='return') {return "return " + grindjs(x[1])};
  if (x[0]==='block')
     {var answer = '{';
      for (var i=1; i<x.length-1; i++)
          {answer += grindjs(x[i]) + '; '};
      answer += grindjs(x[x.length-1]) + '}';
      return answer};
  if (x[0]==='loop')
     {var answer = 'for ';
      answer += '(var ' + x[1] + '=' + x[2] + '; ';
      answer += x[1] + '<' + x[3] + '; ';
      answer += x[1] + '++)\r'
      answer += grindjs(x[4]);
      return answer}
  if (x[0]=== 'function')
     {var answer = 'function ' + x[1] + ' ' + grindjsarglist(x[2]) + '\r';
      answer += '{';
      for (var i=3; i<x.length-1; i++)
          {answer += grindjs(x[i]) + '; '};
      answer += grindjs(x[i]) + '}';
      return answer}
  return x[0] + grindjsarglist(x.slice(1))}

function grindjsarglist (p)
 {var exp = '(';
  if (p.length>0) {exp += grindjs(p[0])};
  for (var i=1; i<p.length; i++)
      {exp = exp + ',' + grindjs(p[i])}
  exp += ')';
  return exp}

function grindjsargs (l)
 {var exp = '';
  if (l.length>0) {exp += grindjs(l[0])};
  for (var i=1; i<l.length; i++)
      {exp = exp + ',' + grindjs(l[i])}
  return exp}

function grindindent (n)
 {var out = '';
  for (var i=0; i<n; i++) {out += ' '};
  return out}

//------------------------------------------------------------------------------
// End of Script
//------------------------------------------------------------------------------
