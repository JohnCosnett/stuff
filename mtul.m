(* ::Package:: *)

BeginPackage["mtul`",{"MaTeX`"}]




CurrentImageGridder::usage = "CurrentImageGridder segments the current image";
clc::usage="clc is schoonship with Clera systema cahecs"

dd::usage ="a dynamically updated context path"

talk::usage = "activate talker now with canceled funk"
edgy::usage = "hold up your hand"
ciwi::usage = "just a celtic swirl on the current image"
mm::usage = "mm[e] does Manipulate n from 1 to 100"
mmm::usage = "mmm[asdf] converts string to expression"

hh::usage = "holdForm clamp"
tt::usage = "MaTeX SHORTCUT "
yyyy::usage = "these packages are fun"
yyy::usage = "function is now not quiet 2"
yy::usage = "the beast of quietn1233ssmtul"
\[Lambda]\[Lambda]::usage = "flatten";
gHPlot::usage = "gHPlot[TT, unitString, color ]";

(*Print["adding directory < prlog > to $path"]*)

Print["activating danger cursor"]

AppendTo[$Path, "/Users/johncosnett/Library/Mathematica/Applications/prlog"]

With[{
  nb := EvaluationNotebook[], c := EvaluationCell[]
},
With[{
  cv := CurrentValue[nb, {"TaggingRules", "LastCursorPosition"}],
  pos := FrontEndExecute@FrontEnd`UndocumentedGetSelectionPacket[nb]
},
With[{
  savePosition := (cv = If[MemberQ[pos, "CharacterRange" -> _],
    Last["CharacterRange" /. pos], False])
},
  SetOptions[nb, CellEventActions :> {
    {"MenuCommand", "HandleShiftReturn"} :> savePosition,
    {"MenuCommand", "EvaluateCells"} :> savePosition,
    PassEventsDown -> True}
  ];
  SetOptions[nb,  CellEpilog :>  If[
    IntegerQ[cv],
    SelectionMove[c, Before, CellContents];
    SelectionMove[nb, Next, Character, cv];
    cv = False;
  ]];
]]]


Begin["`Private`"]






talk := Module[{aaa="start"},


While[ aaa =!= "stop" \[And] aaa=!= $Canceled,
(aaa=InputString[Style["write here",FontSize->24,FontColor->RandomColor[]]];
Print[Style[ToString[FromCharacterCode[9743]],FontColor->Hue[0.79,1,1],FontSize->24],"  ",aaa,"\n"];Speak[aaa]);
(aaa=InputString[Style["write here",FontSize->24,FontColor->Hue[0.31,0.87,0.64]]];
Print[
Style[ ToString[FromCharacterCode[9742]] , FontColor->Red, FontSize->24  ],  "  " , aaa, "\n" ];  Speak[aaa])
]
]



(*FromCharacterCode[3844], FromCharacterCode[9760]*)


\[Lambda]\[Lambda][expr_]:=Flatten[expr]


ciwi:=(s=CurrentImage[];
ImageAdd[CurrentImage[],EdgeDetect[s,10]])


tt[expr_]:=(Needs["MaTeX`"];Style[(Grid[{{"             ",MaTeX[expr]}}]), Magnification -> 2])


hh[expr_]:=HoldForm[expr]


yyy[expr_]:= (Off[Plot::plln];
		Unprotect[Plot]; 
		ClearAttributes[Plot,HoldAll];
		
		expr /. p:{___}->Flatten[p])
	


yyyy[expr_]:= (Off[Plot::plln];Quiet[yyy[expr]])


yy[expr_]:= (Off[Plot::plln];Quiet[yyyy[expr]])




mm[ee_]:=StringJoin["Manipulate[",ToString[InputForm[ee]],",{n,1,100,1}]"]
mm[ee_,n_]:=StringJoin["Manipulate[",ToString[InputForm[ee]],",{n,1,",ToString[n],",1}]"]


mmm[asdf_]:=ToExpression[asdf]


edgy:=(EdgeDetect[CurrentImage[ImageSize->1000],n]~ImageAdd~ColorNegate@CurrentImage[ImageSize->1000])~Manipulate~{{n,5},1,100,1}


clc:=(
		
(*		Remove[`*"];
		Clear[`*"];*)
    Needs["Utilities`CleanSlate`"];
    CleanSlate[];
		Remove["Global`*"];
		ClearAll["Global`*"];
		Clear["Global`*"];
		ClearSystemCache[];
		Unprotect[In, Out]; 
		Clear[In, Out]; 
		Protect[In, Out];
		Print[(N[MemoryInUse[]/1000000])," MegaByte"];
Print["\n\n\n\n\n\n\n\n\n\n\n"]
        
		
	)



dd:= Dynamic@$ContextPath


CurrentImageGridder[]:=(s=
SparseArray[
Join[
Table[({i_,(1+32k/1)}->0),{k,0,7,1}],Table[({(1+32k/1),j_}->0),{k,0,9,1}],
{{_,_}->1}
]

,{320,240}];Rasterize[ArrayPlot[s]]~ImageAdd~CurrentImage[])




gHPlot[TT_, unitString_, color_ : 0] :=
 Module[{\[Mu], \[Sigma],
   p}, {\[Mu], \[Sigma]} = {Mean[TT], StandardDeviation[TT]};
  dist = PDF[NormalDistribution[\[Mu], \[Sigma]], x];
  p = Plot[dist, {x, \[Mu] - 3 \[Sigma], \[Mu] + 3 \[Sigma]},
    Filling -> Axis,
    GridLines -> {{\[Mu] - \[Sigma], \[Mu] + \[Sigma]}, None},
    Ticks -> {{None, {\[Mu] - \[Sigma], "\[Mu]-\[Sigma]"}, {\[Mu],
        "\[Mu]"}, {\[Mu] + \[Sigma], "\[Mu]+\[Sigma]"}, None},
      Automatic}, AxesLabel -> {unitString, "percentProbable"},
    PlotLabel ->
     Style["\[Mu] = " <> ToString[\[Mu]] <> "   \[Sigma] =" <>
       ToString[\[Sigma]], Red]];
  Grid[
   {{Grid[(TT) /. x_Real -> {x},
       FrameStyle -> Directive[color, Dotted], Frame -> All]~
      AccountingForm~2,
     Show[
      Histogram[TT, ChartElementFunction -> "FadingRectangle",
       ChartStyle -> color], p], p}

    }, FrameStyle -> Directive[color, Dotted], Frame -> All]];




End[]
EndPackage[]





