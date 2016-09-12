(* ::Package:: *)

(* :Title: logik *)
(* :Context: logik` *)
(* :Author: johncosnett *)
(* :Date: 2016-06-16 *)
(*Damn I should put this on GIT HUB!*)

BeginPackage["logik`"];

(* control commands*)
assert::usage = "assert[LHS, clauses...] enters a fact or rule
into the database.

assert[  Clue  ]";

(*assert::usage = "assert[  declaration/goal  ]";*)

assertA::usage = "assertA[LHS, clauses...] enters a fact or rule
into the database (at the beginning).";

assertZ::usage = "assertZ[LHS, clauses...] enters a fact or rule
into the database (at the end).";

retract::usage = "retract[ LHS, RHS... ] removes the first matching rule
from the database";


(*badass I am learning some Prolog vocab*)


query::usage = "query[goals...] returns variable bindings
that satisfy the goals";


queryAll::usage = "queryAll[goals... ] prints all satisfying bindings.";


again::usage = "again[]  tries to re-satisfy the last query.";
(* the evaluator has another bash at satisfaction *)


prolog::usage = "prolog starts a Prolog-style dialogue repl";

spy::usage = "spy[sym] turns on tracing for rules attached to sym.";

noSpy::usage = "noSpy[sym] turns off tracing for sym. noSpy[] turns
off tracing for all symbols.";

traceLevel::usage = "traceLevel is the current trace level.
  0 disables all tracing, 2 shows details.";

logicValues::usage = "logicValues[symbol] is the list of logic rules
  attached to symbol.";

rule::usage = "rule[LHS, RHS] is a logic rule.
               rule[LHS] is a logic fact.";





(* NEW SECTION      *)
(*                  *)
(*                  *)
(* logik predicates *)


true::usage = "true always succeeds.";
fail::usage = "fail fails always.";
false::usage = "false fails always.";
cut::usage = "cut succeeds but prevents backtracing.";
repeat::usage = "repeat succeeds and can be redone always.";

and::usage = "and[goals] succeeds if the goals succeed in sequence.";
or::usage = "or[goals] succeeds if one of the goals succeeds.";
not::usage = "not[goal] succeeds if goal fails.";

Equal::usage = Equal::usage <>
  "LHS == RHS succeeds if LHS and RHS can be unified.";

Unequal::usage = Unequal::usage <>
  "LHS == RHS succeeds if LHS and RHS cannot be unified.";



print::usage = "print[exr...] prints the expr and succeeds.";
input::usage = "input[v_, (prompt)] unifies v with an expression read.";
name::usage = "name[v_, l_] succeeds if l is the list of
character codes of the symbol v.";
var::usage = "var[v_] succeeds if v is an uninstantiated variableh.";
nonVar::usage = "nonVar[v_] succeeds if v is an integer.";
ground::usage = "ground[e_] succeeds if e contains no uninstantiated
variables";
integer::usage = "integer[v_] succeeds if v is an integer";
atomic::usage = "atomic[v_] succeeds if v is an atom";
atom::usage = "atom[v_] succeeds if v is an atom other
than a number";
is::usage = "is[eqlist] succeeds if the equations can be solved";

aaassert::usage = "aaassert[r_] succeeds if rule r was entered into
database.";
aaassertA::usage = "aaassertA[r_] succeeds if rule r was entered
into the database (at the beginning).";
aaassertZ::usage = "aaassertZ[r_] succeeds if rule r was entered
into the database (at the end).";
rrretract::usage = "rrretract[r...] succeeds if a rule matching r
was removed from the database.";

run::usage = "run[cmd] evaluates the Mathematica expression cmd
and succeeds if no messages were produced. run[cmd, res] succeeds
if the result of cmd is res.";

trace::usage = "trace always succeeds and turns on full tracing.";
noTrace::usage = "noTrace always succeeds and turns of full tracing";


(* misc *)

yes::usage = "yes indicates a successful query without variables";
no::usage = "no indicates an unsuccessful query";

logic::nohead = "No predicate found as head of `1`.";



(* unit test*)
Print["it's alive!!!"];




Begin["`Private`"];
Print["got to here"];

Needs["uuunify`"];
Needs["lllisp`"];


dispatch[rule[LHS_,___]] := predicate[LHS];
predicate[h_Symbol] := h;
predicate[h_Symbol[___]] := h;
predicate[e_] := (Message[Logic::nohead, e]; Null); (* no predicate *)


makeRule[LHS_] := rule[LHS] /. pattern2Var;
makeRule[LHS_, True] := makeRule[LHS];
makeRule[LHS_, RHS_] := rule[LHS, RHS] /. pattern2Var;
makeRule[LHS_, RHS__] := makeRule[LHS, And[RHS]];

Print["got to B "];

(* IS UNIQUE VARS CHANGED TO UNIQUE>? *)
rename[r_rule]:= uniqueVars[r];

Format[rule[LHS_]] := LHS /. var2Pattern;
Format[r:rule[_, _]]:= Infix[ r /. var2Pattern, " :- "];

logicValues[_Symbol]:= {}; (* for symbols without rules yet *)


(* output variables disregarding anonymous ones *)

outVars[expr_]:= Select[ variables[expr], FreeQ[#, $]& ];

(* statics *)

`tracing;

(* enter a rule into database *)

assert[ LHS_, RHS___] := insertRule[ makeRule[LHS,RHS], Append ];
assertA[ LHS_, RHS___] := insertRuls[ makeRule[LHS, RHS], Prepend ];

insertRule[r_, op_] :=
    With[{h = dispatch[r]},
      If[  h === Null, Return[$Failed] ];
      logicValues[h] ^= op[ logicValues[h], r ];
    ];

assertZ = assert;

retract[ args__ ] :=
    Module[{res},
      res = RemoveOne[ makeRule[args] ];
      If[ res === $Failed, res, Null];
    ];

removeOne[ r_rule ] :=
    Module[{h = dispatch[r], lv, i},
      lv = logicValues[h];
      For[ i = 1, i <= Length[lv], i++,
        bind  = unify0[ lv[[i]], r ];
        If[ bind === $Failed, Continue[] ];
        logicValues[h] ^= Drop[lv, {i}];
        Return[bind]
      ];
      $Failed
    ];

(* logic evaluator qeval[goal, state] *)
(* return value is neither {bindings, state},
 {$Failed, finalState} or $Cut *)

`initialState; (* special state the first call of goal *)
`finalState;   (* special state if no more backtracing is possible *)
`$Cut;         (* cut encountered, treated mostly like failure *)


noBindings = {};
yesss = {noBindings, finalState};  (* non-redoable success *)
noooo = ({$Failed, finalState});
noCut = $Cut;

bindings[{bind_, _}] := bind;
state[{_, state_}] := state;
bindings[$Cut] = $Failed;
state[$Cut] = finalState;

failedQ[res_] := bindings[res] === $Failed;
cutQ[$Cut]   := True;
  cutQ[_] = False;


finalState/: qeval[ _, finalState ] := noooo; (* speedup, but be careful! *)

qeval[ True, initialState ] := yesss;
qeval[ False, initialState ] := noooo;
fail/: qeval[ fail, initialState ] := noooo; (* cannot equate to False *)
true/: qeval[ true, initialState ] := yesss; (* cannot equate  to True *)

protected = Unprotect[And, Or, Not, Equal, Unequal];

(* And: state is triplet
  {result of first clause, instance of rest, rest state} *)

And/: qeval[ and:And[g1_, goals__], initialState ] :=
    Module[{res},
      res = qeval[g1, initialState]; (* call first one to initialize things *)
      If[ failedQ[res], Return[res] ]; (* failure *)
      qeval[ and, {res, And[goals] //. bindings[res], initialState} ]
    ];

And/: qeval[ And[g1_, goals__], {res10_, rest0_, stater0_} ] :=
    Module[{res1 = res10, rest = rest0, stater = stater0, res, binds},
      While[ True,
        res = qeval[ rest, stater ];
        If[ !failedQ[res],
          binds = closure[bindings[res1], bindings[res]];
          Return[{binds, {res1, rest, state[res]}}];
        ];
        If[ cutQ[res], Return[res] ]; (* no backtracking in this case*)
        (* try first one again *)
        res1 = qeval[g1, state[res1]];
        If[ failedQ[res1], Return[res1] ];
        stater = initialState; (* reset for next attempt *)
        rest = And[goals] //. bindings[res1] (* instantiate *)
      ];
    ];

(* Or: state is pair {firststate, nextstate} *)

Or/: qeval[ or_Or, initialState ] :=
    qeval[ or, {initialState, initialState} ];

Or/: qeval[ Or[q1_, goals__], {state1_, stater_} ] :=
    Module[{res},
      (* try first clause *)
      res = qeval[g1, state1];
      If[ !failedQ[res],
        Return[{bindings[res], {state[res], initialState}}] ];
      If[ cutQ[res], Return[res] ]; (* no alternatives in this case*)
      (* try rest of them*)
      res = qeval[ Or[goals], stater];
      If[ failedQ[res], Return[res] ];
      {bindings[res], {finalState, state[res]}} (* dont try first one again *)
    ];

(* Not: state is unused *)

Not/: qeval[Not[g_], initialState ] :=
    If[ failedQ[ qeval[g, initialState] ], yesss, noooo ];

(* equation solving: state is list of remaining solutions *)
(* a solution is already a list of rules! *)

is/: qeval[ t:is[ eq_ ] , initialState ] :=
        qeval[ t, Solve[ eq, variable[eq] ] ];

is/: qeval[ _is , {} ] := noooo; (* no more solutions *)
is/: qeval[ _is , sols_List ] := {First[sols], Rest[sols]};

(* I/O *)

input/: qeval[ input[ v_, prompt_:"? " ], initialState ] :=
    Module[{in},
      in = Input[prompt] /. pattern2Var;
      If[ in === EndOfFile,
        noooo,
        {unify0[v, in], initialState }(* can be redone *)
      ]
    ];

print/: qeval[ print[args___], initialState ] := (Print[args]; yesss );

(* equality is unifiction *)

Equal/: qeval[ e1_ == e2_, initialState ] :=
    Module[{u},
      u = unify0[e1, e2];
      If[ u === $Failed, noooo, {u, finalState} ]
    ];

(* unequality: non-unification (necessary because of !a==b --> a != b) *)

Unequal/: qeval[ e1_ != e2_, initialState ] :=
    If[ unify0[e1, e2] === $Failed, yesss, noooo ];

(* name: break atom into characters *)

list2Nest[nil] := {};
list2Nest[c_cons] := {car[c], list2Nest[cdr[c]]};
list2List[l_] := Flatten[list2Nest[l]];
listQ[nil] = True;        (* this atom is also a list *)
listQ[l_cons] := listQ[cdr[l]];
listQ[_] = False;

name/: qeval[ name[sym_Symbol, l_], initialState ] :=
    Module[{charcodes = ToCharacterCode[ ToString[sym]], bind},
      bind = unify0[list @@ charcodes, l];
      If[ bind === $Failed, noooo, {bind, finalState} ]
    ];

name/: qeval[ name[v_, l_?listQ], initialState ] :=
    Module[{chars = list2List[l]},
      sym = FromCharacterCode[chars];
      If[ Head[sym] =!= String , Return[noooo] ];
      sym = ToExpression[sym];
      If[ Head[sym] =!= Symbol , Return[noooo] ];
      bind = unify0[v, sym];
      If[ bind === $Failed, noooo, {bind, finalState} ]
    ];

(* var: if argument is uninstantiated variable *)

var/: qeval[ var[ v_var ], initialState ] := yesss;
var/: qeval[ var[ var[_], _ ]] := noooo;

(* ground: no variables *)

ground/: qeval[ ground[expr_ ], initialState ] :=
    If[ variables[expr] === {}, yesss , noooo];

(* =.., functor, arg *)

(* aaassert *)

aaassert/: qeval[ aaassert[r___], initialState ] :=
    If[ insertRule[makeRule[r], Append] === $Failed, noooo, yesss ];

aaassertA /: qeval[ aaassertA[r___], initialState ] :=
    If[ insertRule[makeRule[r], Prepend] === $Failed, noooo, yesss];

rrretract/: qeval[rrretract[args___], initialState ] :=
    Module[{r = makeRule[args], bind},
      bind = removeOne[r];
      If[ bind === $Failed, noooo, {bind, initalState} ]
    ];

(* cut *)

cut/: qeval[ cut, initialState ] := {noBindings, cutState}; (* success *)
cut/: qeval[ cut, cutState ]     := noCut;                   (* fail/ cut *)

(* run: evaluate Mathemtica expression *)

SetAttributes[run, HoldFirst];

run/: qeval[ run[cmd_], initialState ] :=
    Module[{ret},
      ret = Check[cmd, $Failed];
      If[ ret === $Failed, noooo, yesss ]
    ];

run/: qeval[ run[ cmd_, res_], initialState ] :=
    Module[{ret},
      ret = cmd; (* eval it here *)
      {unify0[ret, res], finalState}
    ];


(* apply rules: state is triplet { rest of rules, instance of first rule, its
state} *)

qeval[ expr_ initialState ] :=
    With[{rules = logicValues[predicate[expr]]},
      If[ Length[rules] == 0, Return[noooo] ];
      qeval[ expr, {Rest[rules], rename[First[rules]], initialState} ]
    ];

qeval[ expr_ {rules0_, inst0_, rstate0_} ] :=
    Module[{rules = rules0, inst = inst0, rstate = rstate0, res},
      traceGoal[expr];
      While[True,
        res = tryRule[ expr, inst, rstate ];
        If[ !failedQ[res],
          traceGoalYes[expr, bindings[res]];
          Return[{bindings[res], {rules, inst, state[res]}}] ];
        If[ cutQ[res], traceGoalNo[expr, res];
          Return[noooo] ]; (* use and discard cut *)
        (* else try next rules *)
        If[ Length[rules] == 0, Break[] ]; (* no more *)
        inst = rename[First[rules]];
        rstate = initialState;
        rules = Rest[rules];
      ];
      traceGoalNo[expr, noooo];
      noooo;
    ];

(* closed world *)

qeval[ _, initialState ] := noooo;
qeval[ g_, s_ ] := Message[Head[g]::sprd, g, s];

General::sprd = "qeval error: Goal `1` redo attempted without prior init,
state is `2`.";

(* try a rule: state is {LHS unifer, instance of RHS, state of RHS qeval} *)

finalState/: tryRule[ _, _, finalState ] := noooo

(* for facts *)

tryRule[ expr_, r:rule[LHS_], initialState ] :=
    Module[{bind, inst, res},
      bind = unify0[ expr, LHS ];           (* unify LHS *)
      If[ bind === $Failed, Return[noooo] ];   (* does not unify *)
      bind = closure[bind];
      traceCall[r, True, initialState];
      traceReturn[r, bind];
      {bind, finalState}
    ];

(* for rules proper *)

tryRule[ expr_, r:rule[LHS_,RHS_ ], initialState ] :=
    Module[{bind, res},
      bind = unify0[ expr, LHS ];           (* unify LHS *)
      If[ bind === $Failed, Return[noooo] ];   (* does not unify *)
      tryRule[ expr, r, {bind, RHS //. bind, initialState} ]
    ];

tryRule[ expr_, r_rule, {bind_, inst_, stater_} ] :=
    Module[{res, outBind},
      traceCall[r, inst, stater];
      res = qeval[ inst, stater ]; (* recursion *)
      If[ failedQ[res], traceFail[r]; Return[res] ];
      outBind = closure[bind, bindings[res]];
      traceReturn[r, outBind];
      {outBind, {bind, inst, state[res]}}
    ];

(* trace *)
traceLevel = 1;
`traceIndent = 0;

traceGoal[expr_] /; traceLevel > 0 && tracing[predicate[expr]] := (
    traceIndent++;
    Print[ spaces[traceIndent], "goal is ", expr /. var2Pattern ];
  );

traceGoalYes[expr_, bind_] /; traceLevel > 0 && tracing[predicate[expr]] :=(
    Print[ spaces[traceIndent], "yes, with ",
      bindingsFor[bind, outVars[expr]] /. var2Symbol ];
    traceIndent--;
);


traceGoalNo[expr_, res_] /; traceLevel >0 && tracing[predicate[expr]] := (
    Print[ spaces[traceIndent], If[cutQ[res], "no (cut).", "no."] ];
    traceIndent--;
);

traceCall[r_, new_, s_] /; traceLevel > 1 && tracing[dispatch[r]] := (
    traceIndent++;
    Print[ spaces[traceIndent],
      If[s === initialState, ">call: ", ">redo: "],
      r ];
    If[ new =!= True,
      Print[ spaces[ traceIndent], "+new goal: ", new ];
    ]
    );

traceReturn[r_, bind_] /; traceLevel > 1 && tracing[dispatch[r]] := (
    Print[ spaces[traceIndent], "<ret:  ", bind ];
    traceIndent--;
);

traceFail[r_] /; traceLevel > 1 && tracing[dispatch[r]] := (
    Print[ spaces[traceIndent], "<failed" ];
    traceIndent--;
);

spyPoints = {};

spy[ h_Symbol ] :=
    (h /: tracing[h] = True; spyPoints = Union[spyPoints, {h}]; );

noSpy[ h_Symbol ] :=
    (h/: tracing[h] =. ;spyPoints = Complement[spyPoints, {h}];);

noSpy[] := (noSpy /@ spyPoints;);

tracing[_] := False;

spaces[n_] := Nest[# <> " "&, "", 2n];

trace/: qeval[ trace, initialState ] := (tracing[_] := True; yesss);
noTrace/: qeval[ noTrace, initialState ]:= (tracing[_] := False; yesss);


(* queries user level *)

`redoExpr;
`redoState;

reset := (
    redoState = finalState;
    traceIndent = 0;
    tracing[_] := False;
    );

query[ goal_ ] :=
    Module[{g = goal /. pattern2Var},
        reset;
        {redoExpr, redoState} = {g, initialState};
        again[]
    ];

query[ goals___ ] := query[ And[ goals] ]; (* several goals possible *)

queryAll[ goal___ ] :=
    Module[{res},
        res = query[ goal ];
        While[ res =!= no, Print[res]; res = again[] ];
    ];

again[] :=
    Module[{res, outBind},
        res = qeval[ redoExpr, redoState ];
        redoState = state[res];
        If[ failedQ[res],
            no
          ,
            outBind = bindingsFor[ bindings[res], outVars[redoExpr] ];
          If[ outBind === noBindings, yes, outBind /. var2Symbol ]
        ]

    ];

(* more predefined predicates *)

assert[ nonVar[x_], !var[x_] ];

assert[ repeat ];

assert[ repeat, repeat ];

and = And;
or = Or;
not = Not;
aaassertZ = aaassert;
false = fail;

(* implemented in terms of Mathematica predicates *)

integer[e_] := IntegerQ[e];
atomic[e_]  := AtomQ[e];
atom[e_]    := atomic[e] && !NumberQ[e];

(* main loop Prolog-style *)

prompt =  "?- "     ;
nl     := Print[""] ;
aaagain  := " ?"      ;

prolog :=
    Module[{queery},
      While[True,
        queery = Input[prompt]             ;
        If[ queery === EndOfFile, Break[] ];
        res = query[ queery ]              ;
        WriteString[ $Output, res ]       ;
        While[ res =!= no,
          cont = InputString[aaagain]       ;
          If[ cont =!= ";", Break[] ]     ;
          res = again[];                   ;
          WriteString[ $Output, res ]     ;
        ];
        If[ res === no,  nl ];
        nl;
      ] ;
    ];

Protect[ Evaluate[protected] ];

End[] (* `Private` *);

Protect[ Evaluate[$Context <> "*"]];
Unprotect[ traceLevel ];

EndPackage[];
