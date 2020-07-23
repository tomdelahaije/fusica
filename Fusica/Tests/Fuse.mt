(*
	Copyright 2020 Tom Dela Haije

	Licensed under the Apache License, Version 2.0 (the "License");
	you may not use this file except in compliance with the License.
	You may obtain a copy of the License at

		http://www.apache.org/licenses/LICENSE-2.0

	Unless required by applicable law or agreed to in writing, software
	distributed under the License is distributed on an "AS IS" BASIS,
	WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
	See the License for the specific language governing permissions and
	limitations under the License.
*)

(*Fuse symbols*)

f[x_Integer] := x;
f[4] := 0;
g[x_] := x^2;
fg = Fuse[f, g];

Test[
	Context[Evaluate[fg]]
	,
	"Fusica`Shadows`"
	,
	TestID->"Fuse-20200603-K1G6M3"
];

Test[
	fg /@ Range[1, 4, 1/2]
	,
	{1, 9/4, 2, 25/4, 3, 49/4, 0}
	,
	TestID->"Fuse-20200603-D5S1T5"
];

(*Fuse with fused symbol*)
h[5] := 2;
fgh = Fuse[fg, h];

Test[
	Context[Evaluate[fgh]]
	,
	"Fusica`Shadows`"
	,
	TestID->"Fuse-20200603-I9U4P0"
];

Test[
	fgh /@ Range[1, 5, 1/2]
	,
	{1, 9/4, 2, 25/4, 3, 49/4, 0, 81/4, 2}
	,
	TestID->"Fuse-20200603-R9B7P6"
];

(*Flatten symbols*)

hfg = Fuse[h, fg, g, f, g, h];

Test[
	Context[Evaluate[hfg]]
	,
	"Fusica`Shadows`"
	,
	TestID->"Fuse-20200603-D8Y0H8"
];

Test[
	hfg
	,
	Fuse[h, f, g]
	,
	TestID->"Fuse-20200603-T9X7Z1"
];

(*Alias*)

Test[
	Diamond[f,g] == (f\[Diamond]g) == Fuse[f, g] == fg
	,
	True
	,
	TestID->"Fuse-20200603-J5Y6Q2"
];

(*Definition updating*)

f[1] = 3;

Test[
	fg[1]
	,
	3
	,
	TestID->"Fuse-20200603-D5V6R0"
];

(*Definition ordering*)

g[2] = 3;

Test[
	fg /@ Range[1, 3]
	,
	{3, 3, 3}
	,
	TestID->"Fuse-20200603-O4A1O1"
];

(*Shadow attributes*)

Test[
	fg[1] := 10;
	,
	Null
	,
	{SetDelayed::write}
	,
	TestID->"Fuse-20200603-V0A5H3"
]
Test[
	Attributes[Evaluate@fg]
	,
	{Protected, ReadProtected, Temporary}
	,
	TestID->"Fuse-20200603-G5R3I8"
];

(*Recursive definitions*)

(head : recursiveFusible)[n_Integer?Positive] := head[n - 1]
Test[
	Fuse[h, recursiveFusible][10]
	,
	2
	,
	TestID->"Fuse-20200603-K9J8F4"
];

(*Pattern matching*)

Test[
	MatchQ[Fuse[h], h]
	,
	False
	,
	TestID->"Fuse-20200603-Y3F8K0"
];

(*Flattening*)

Test[
	Fuse[f, Fuse[g, h]] == fgh == Fuse[f, g, h]
	,
	True
	,
	TestID->"Fuse-20200603-W2J9X1"
];

(*Outdated definitions with Set*)

k[5] = 8;
h = Fuse[k];

Test[
	{h[5], fgh[5]}
	,
	{8, 2}
	,
	TestID->"Fuse-20200603-R9Q5G1"
];

(*Updated definitions with SetDelayed*)

fgh := Fuse[f, g, h];
h := Fuse[k];
k[5] = 10;

Test[
	fgh[5]
	,
	10
	,
	TestID->"Fuse-20200603-H1L6F2"
];

(*Self-fused symbols*)

f := Fuse[Unevaluated[f], g]
h =.;
g := Fuse[Unevaluated[g], h]

Test[
	f /@ Range[1, 4, 1/2]
	,
	{3, 9/4, 3, 25/4, 3, 49/4, 0}
	,
	TestID->"Fuse-20200603-H5R8N7"
];

Test[
	g /@ Range[1, 4, 1/2]
	,
	{1, 9/4, 3, 25/4, 9, 49/4, 16}
	,
	TestID->"Fuse-20200603-N6I0S3"
];

(*Add definitions with HoldPattern*)

Test[
	f[3] = \[Pi];
	,
	Null
	,
	{Set::write}
	,
	TestID->"Fuse-20200603-T9L7X6"
];

HoldPattern[f][3] = \[Pi];

Test[
	f[3]
	,
	\[Pi]
	,
	TestID->"Fuse-20200603-V5N5L7"
];

(*Add definitions with toggle*)

$i = True; 
i := Block[{$i}, Fuse[i, f]] /; $i;

Block[{$i}, i[1] = Sqrt[2]];

Test[
	i[1] = Sqrt[2];
	,
	Null
	,
	{Set::write}
	,
	TestID->"Fuse-20200603-E1A4Y5"
];

Test[
	i /@ Range[1, 5, 1/2]
	,
	{Sqrt[2], 9/4, 3, 25/4, \[Pi], 49/4, 0, 81/4, 2}
	,
	TestID->"Fuse-20200603-C1U6C7"
];

(*Infinite recursion*)
selfFusedWithoutUnevaluated := Fuse[selfFusedWithoutUnevaluated];

Test[
	Hold[Evaluate[Fuse[selfFusedWithoutUnevaluated]]]
	,
	Hold[Fuse[selfFusedWithoutUnevaluated]]
	,
	{$RecursionLimit::reclim2}
	,
	TestID->"Fuse-20200603-L9L6B5", EquivalenceFunction -> MatchQ
];

(*Attributes mismatch*)
Attributes[symbolWithAttr] = HoldAll;

Test[
	fusedWithAttr = Fuse[f, symbolWithAttr];
	,
	Null
	,
	{Fuse::attrmm}
	,
	TestID->"Fuse-20200603-H4M0D8"
];

(*Wrong input*)

Test[
	Hold[Evaluate[Fuse[3]]]
	,
	Hold[Fuse[3]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200603-T0X4Y2", EquivalenceFunction -> MatchQ
];

Test[
	Hold[Evaluate[Fuse[symbol, 3]]]
	,
	Hold[Fuse[symbol, 3]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200604-F3K5G6", EquivalenceFunction -> MatchQ
];

Test[
	Hold[Evaluate[Fuse[3, Fuse[3]]]]
	,
	Hold[Fuse[3, Fuse[3]]]
	,
	{Fuse::ssym, Fuse::ssym}
	,
	TestID->"Fuse-20200605-J1B3S1"
];

Test[
	Hold[Evaluate[Fuse[3, 3]]]
	,
	Hold[Fuse[3, 3]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200605-U3G8L3"
];

Test[
	Hold[Evaluate[Fuse[symbol, Fuse[3]]]]
	,
	Hold[Fuse[symbol, Fuse[3]]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200605-B0G1X0"
];

Test[
	Hold[Evaluate[Fuse[s, Fuse[s, 3]]]]
	,
	Hold[Fuse[s, Fuse[s, 3]]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200605-Z6Y5I7"
];

Test[
	Hold[Evaluate[Fuse[Fuse[3]]]]
	,
	Hold[Fuse[Fuse[3]]]
	,
	{Fuse::ssym}
	,
	TestID->"Fuse-20200605-I5C7D5"
];
