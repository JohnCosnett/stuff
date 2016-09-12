(* ::Package:: *)

(* Mathematica Package *)
(* Created by Mathematica Plugin for IntelliJ IDEA *)

(* :Title: odex *)
(* :Context: odex` *)
(* :Author: johncosnett *)
(* :Date: 2016-06-04 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: *)
(* :Copyright: (c) 2016 johncosnett *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["odex`"]

Needs["mtul`"]
(* Exported symbols added here with SymbolName::usage *)
sizeMoGraph::usage = "sizeMoGraph[solution, OrdinaryDifferentialEquation] = creates
an earthquake needle plot";
sizeMoGraph2::usage = "sizeMoGraph2[solution, OrdinaryDifferentialEquation] = creates
an earthquake needle plot";

sizeMoGraph4::usage = "sizeMoGraph4[solution, placeholder] = sensitivity guages";
sizeMoGraph3::usage = "sizeMoGraph3[nonTrig, nameOfPlot] = ships sail";


Begin["`Private`"]




sizeMoGraph[f_, equation_] := (Module[{$minn,$maxx},

   $minn = FindMinimum[f[z], {z, -1.0}];
   $maxx = FindMaximum[f[z], {z, 1.0}];

   Manipulate[

     Grid[{{

        ThermometerGauge[f[xx], {$minn, $maxx},
         GaugeStyle -> Purple],


        Show[
         Plot[f[xx + i], {i, -2 Pi, 2 Pi}, ImageSize -> 350,
          PlotStyle -> Green,
          PlotLabel -> Style[MaTeX[hh[equation]]]],
         Graphics[{Purple, PointSize[0.03], Point[{0, f[xx]}]}]]


        }}],

     {xx, -2 \[Pi], 2 \[Pi], 0.1}]]);







sizeMoGraph2[f_, equation_] := (Module[{$minn,$maxx},

   $minn = FindMaximum[f[z], {z, 1.0}] ;

   $maxx = FindMinimum[f[z], {z, -1.0}] ;

   ListAnimate@Table[


     Grid[{{

       ThermometerGauge[f[xx], {$minn, $maxx},
         GaugeStyle -> Purple],


        Show[
         Plot[f[xx + i], {i, -2 Pi, 2 Pi}, ImageSize -> 350,
          PlotStyle -> Green,
          PlotLabel -> Style[MaTeX[hh[equation]]]],
         Graphics[{Purple, PointSize[0.03], Point[{0, f[xx]}]}]]


        }}],

     {xx, -2 \[Pi], 2 \[Pi], 0.1}]]);



sizeMoGraph3[f_, equation_] :=

  (Module[{$minn, $maxx},
    $minn = f[-2 Pi](*FindMinimum[f[z],{z,-1.0}]*);
    $maxx = f[2 \[Pi]](*FindMaximum[f[z],{z,  1.0}]*);
    ListAnimate@Table[
      Grid[{{
         ThermometerGauge[f[xx], {$minn, $maxx},
          GaugeStyle -> Purple],
         Show[Plot[
           Table[f[xx + i + j], {j, -Pi, Pi}], {i, -2 Pi, 0},
           PlotRange -> {{-5, 5}, {-0, $maxx}}, ImageSize -> 350,
           PlotStyle -> Purple,
           PlotLabel -> Style[MaTeX[hh[equation]]]],

          Graphics[{Purple, PointSize[0.03], Point[Table[{0, f[xx+j]},{j,-Pi,Pi}]]}]]
         }}],
      {xx, -2 \[Pi], 2 \[Pi], 0.1}]]);



sizeMoGraph4[function_, stuff_] := Module[{},


   Manipulate[

    With[{f = function},




     Column[{Row[{


          Plot[f[t], {t, -4, 4},
           Epilog -> {PointSize[Large], Red, Point[{p, f[p]}]},
           ImageSize -> Medium],
          ThermometerGauge[f[p], {-2, .5}, ImageSize -> 200]}]


        Row[

         {

          (*AngularGauge[(f[x]/.x\[Rule]p),{-3,3},
          GaugeLabels\[Rule]{Placed["Y Quantity",{.5,.7}],
          Automatic}],*)


          AngularGauge[(D[f[x], {x, 1}] /. x -> p), {-3, 3},
           GaugeLabels -> {Placed["Derivative[Y]", {.5, .7}],
             Automatic}]}],
       }, Center]],



    {{p, 0}, -4, 4, AngularGauge[##, ImageSize -> 125] &},
    ControlPlacement -> Top

    (*{{p,-3.5},-4,2}*)]
   ];








End[] (* `Private` *)

EndPackage[]
