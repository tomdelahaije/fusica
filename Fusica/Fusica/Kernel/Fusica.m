(*Begin Fusica package*)
BeginPackage["Fusica`", {"GeneralUtilities`"}];


(*Unprotect symbols*)
Unprotect[
	$Tracker,
	CopyTo,
	Fuse,
	FusePattern
];


(*Usage messages*)
SetUsage[$Tracker, 
	"$Tracker is a toggle variable which enables the updating behavior of Fuse when set to True."
];
SetUsage[CopyTo, 
	"CopyTo[target$, symbol$] copies all associated definitions from symbol$ to target$.",
	"CopyTo[target$, {symbol$1, symbol$2, $$}] copies all associated definitions from symbol$1, symbol$2, $$ to target$.",
	"CopyTo[symbol$] is the same as CopyTo[symbol$, symbol$]."
];
SetUsage[Fuse, 
	"Fuse[symbol$1, symbol$2, $$] returns a temporary symbol whose definition is generated from the values, options, and attributes associated to symbol$1, symbol$2, $$."
];
SetUsage[FusePattern, 
	"FusePattern[pattern$] represents a pattern object that matches shadow symbols created by Fuse[args$], where args$ match pattern$."
];
	
(*Messages*)
CopyTo::locked 							= "Symbol `1` is locked.";
CopyTo::attrmm 		= Fuse::attrmm 		= "Warning: attributes mismatch between symbols `1`.";
CopyTo::kernsym 	= Fuse::kernsym		= "Warning: symbol `1` is implemented in the kernel and will be fused using aliasing, which may not reproduce the expected behavior exactly.";
CopyTo::kernform 	= Fuse::kernform 	= "Warning: formatting values for symbol `1` are implemented in the kernel and cannot be fused.";
Fuse::trackfail 						= "Warning: the value `1` added to the shadow of the symbols `2` may prevent the shadow from updating.";

Off[Fuse::kernform];


(*Begin settings context*)
Begin["`Settings`"];


	(*$Alias*)
	SetUsage[$Alias, "$Alias contains the symbol that is used as an alias for Fuse."];
	If[!ValueQ[$Alias], $Alias = Diamond];
	
	(*$ShadowBoxes*)
	SetUsage[$ShadowBoxes, "$ShadowBoxes contains a function that defines the default formatting of shadow symbols."];
	If[!ValueQ[$ShadowBoxes], 
		
		$ShadowBoxes = With[{alias = $Alias}, 
			
			Function[
				Null, 
				If[Length[Hold[##]] > 1, ToBoxes[Unevaluated[alias[##]]], ToBoxes[Unevaluated[##]]], 
				HoldAllComplete
			]
			
		]
		
	];
	
	(*$ShadowContext*)
	SetUsage[$ShadowContext, "$ShadowContext contains a string with the context used for shadow symbols created by Fuse."];
	If[!ValueQ[$ShadowContext], $ShadowContext = "Fusica`Shadows`"];
	
	
(*End settings context*)
End[];


(*Begin private context*)
Begin["`Private`"];

	
	(*Support functions*)
	
	(*$Update*)
	SetUsage[$Update, "$Update is a toggle variable that can be used to block the overloaded definitions of Update for shadow symbols."];
	$Update = True;
	
	(*AddKernelCodeAliasing*)(*Add evaluation check*)(*Use argument pattern in syntaxinformation to create more specific definitions*)
	SetUsage[AddKernelCodeAliasing, "AddKernelCodeAliasing[head$, symbol$, definitions$] appends aliasing definitions to definitions$ for a symbol symbol$ that is implemented directly in the kernel."];
	SetAttributes[AddKernelCodeAliasing, HoldAll];
	AddKernelCodeAliasing[CopyTo | Fuse, _Symbol ? System`Private`HasNoCodesQ, definitions : Language`DefinitionList[___]] := definitions;
	AddKernelCodeAliasing[head : CopyTo | Fuse, symbol_Symbol, definitions : Language`DefinitionList[___]] := Module[{output = definitions},
		
		Message[head::kernsym, HoldForm[symbol]];
		
		If[System`Private`HasOwnCodeQ[symbol], 		output = With[{defs = output}, AddOwnCodeAlias[head, symbol, defs]]];
		If[System`Private`HasDownCodeQ[symbol], 	output = With[{defs = output}, AddDownCodeAlias[head, symbol, defs]]];
		If[System`Private`HasSubCodeQ[symbol], 		output = With[{defs = output}, AddSubCodeAlias[head, symbol, defs]]];
		If[System`Private`HasUpCodeQ[symbol], 		output = With[{defs = output}, AddUpCodeAlias[head, symbol, defs]]];
		If[System`Private`HasPrintCodeQ[symbol], 	output = With[{defs = output}, AddPrintCodeAlias[head, symbol, defs]]];
		
		output
		
	];
	SetAttributes[AddOwnCodeAlias, HoldAll];
	AddOwnCodeAlias[CopyTo | Fuse, symbol_Symbol, Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {other1__, OwnValues -> ({ownvalues___} | ownvalue_), other2__}, right___]] := 
		Language`DefinitionList[
			left,
			HoldForm[symbol] -> {
	  			other1,
	  			OwnValues -> {ownvalues, ownvalue, HoldPattern[symbol] :> symbol},
	  			other2
	  		},
			right
		];
	SetAttributes[AddDownCodeAlias, HoldAll];
	AddDownCodeAlias[CopyTo | Fuse, symbol_Symbol, Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {other1__, DownValues -> ({downvalues___} | downvalue_), other2__}, right___]] := 
		Language`DefinitionList[
			left,
			HoldForm[symbol] -> {
	  			other1,
	  			DownValues -> {downvalues, downvalue, HoldPattern[symbol[args___]] :> symbol[args]},
	  			other2
	  		},
			right
		];
	SetAttributes[AddSubCodeAlias, HoldAll];
	AddSubCodeAlias[CopyTo | Fuse, symbol_Symbol, Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {other1__, SubValues -> ({subvalues___} | subvalue_), other2__}, right___]] := 
		Language`DefinitionList[
			left,
			HoldForm[symbol] -> {
	  			other1,
	  			SubValues -> {subvalues, subvalue, HoldPattern[symbol[args1___][args2___]] :> symbol[args1][args2]},
	  			other2
	  		},
			right
		];
	SetAttributes[AddUpCodeAlias, HoldAll];
	AddUpCodeAlias[CopyTo | Fuse, symbol_Symbol, Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {other1__, UpValues -> ({upvalues___} | upvalue_), other2__}, right___]] := 
		Language`DefinitionList[
			left,
			HoldForm[symbol] -> {
	  			other1,
	  			UpValues -> {upvalues, upvalue, HoldPattern[h_[l___, symbol, r___]] :> h[l, symbol, r]},
	  			other2
	  		},
			right
		];
	SetAttributes[AddPrintCodeAlias, HoldAll];
    AddPrintCodeAlias[head : CopyTo | Fuse, symbol_Symbol, definitions : Language`DefinitionList[___]] := (Message[head::kernform, HoldForm[symbol]]; definitions);
	
	(*CachedDefinitions*)
	SetUsage[CachedDefinitions, "CachedDefinitions[shadow$] is used to store cached definitions for shadow$."];
	SetAttributes[CachedDefinitions, HoldAll];
	
	(*FlattenShadows*)
	SetUsage[FlattenShadows, "FlattenShadows[symbols$] replaces all shadow symbols in the list symbols$ with the symbols they combine, and returns Hold[flat], where flat is the sequence of flattened symbols."];
	SetAttributes[FlattenShadows, HoldAll];
	FlattenShadows[{symbols__Symbol}] := FlattenShadows[{}, {}, {symbols}]; 
	FlattenShadows[
		{done___Symbol}, {shadows___Symbol}, {symbol_Symbol, remainder___Symbol}
	] /; MemberQ[Hold[done, shadows], HoldPattern[symbol]] := FlattenShadows[{done}, {shadows}, {remainder}];
	FlattenShadows[
		{done___Symbol}, {shadows___Symbol}, {symbol_Symbol, remainder___Symbol}
	] /; ShadowQ[symbol] := FlattenShadows[{done}, {shadows, symbol}, {##, remainder}] & @@ Unevaluated /@ Light[symbol];
	FlattenShadows[
		{done___Symbol}, {shadows___Symbol}, {symbol_Symbol, remainder___Symbol}
	] := FlattenShadows[{done, symbol}, {shadows}, {remainder}];
	FlattenShadows[{symbols__Symbol}, {___Symbol}, {}] := Hold[symbols];
		
	(*InheritanceRule*)
	SetUsage[InheritanceRule, "InheritanceRule[shadow$, symbol$] returns a dispatch table that can be used to transform a list of definitions for symbol$ into a set of evaluatable definitions for shadow$."];
	(*InheritanceRule provides a rule that transforms Rule/RuleDelayed descriptions of definitions for a source symbol, to TagSetDelayed definitions for a shadow symbol. All occurrences of the source symbol on the left hand side are replaced by the inert Substitute[shadow], which will be replaced by the shadow itself in PrepareDefinitions, except for source symbols occurring in patterns wrapped in Verbatim. The Substitute wrapper is used to ensure that users can explicitly exclude definitions that already contain a shadow symbol in their lhs pattern, but whose source symbol is wrapped in Verbatim. Any definition that does not contain a Substitute[shadow] in the lhs is removed in PrepareDefinitions. It is still possible that a user has a definition where the substitutable source symbol is too deep for an assignment -- which would normally prevent the definition from applying to the shadow -- while there is also a shadow symbol present at a more superficial level. In this case we explicitly allow the definition to remain. Ideally we would have both TagSetDelayed and TagSet rules, but at the moment this leads to problems with some (uncommon) definition patterns being copied incorrectly. (The source of these problems is a difference between TagSet and Set in their handling of values wrapped in Unevaluated: f/:f[0]=Unevaluated[1+1] is not the same as f[0]=Unevaluated[1+1]. TagSetDelayed is possibly slower in certain cases, but I have not found examples of definitions that are not copied properly.)*)
	SetAttributes[InheritanceRule, HoldAll];
	InheritanceRule[shadow_Symbol, symbol_Symbol] := InheritanceRule[shadow, symbol] = Dispatch[ 
		{
     		
     		(Rule|RuleDelayed)[Verbatim[HoldPattern][pattern_], value_] :> With[
     			{
     				lhs = Unevaluated @@ (Hold[pattern] /. {arg_Verbatim :> arg, HoldPattern[symbol] :> Substitute[shadow]})
     			},
       
       			(*This would ideally be replaced with TagSet in the case of Rule, but a bug in TagSet prevents this. (f/:f[0]=Unevaluated[1+1] is not the same as f[0]=Unevaluated[1+1].)*)
       			TagSetDelayed[shadow, lhs, value] /; True
       		
       		]
       		
     	}
  	];
  	
	(*Light*)
	SetUsage[Light, "Light[shadow$] returns Hold[symbol$1, symbol$2, $$], where symbol$1, symbol$2, $$ is the ordered set of source symbols to which the shadow symbol shadow$ is associated."];
	SetAttributes[Light, HoldAll];
	
	(*LightFuse *)
	SetUsage[LightFuse, "LightFuse[symbol$1, symbol$2, $$] flattens the evaluated arguments symbol$1, symbol$2, $$ and returns a shadow symbol for the resulting symbols."];
	(*LightFuse immediately forwards to Shadow if symbols already have a shadow symbol (as checked with LightQ). If not, the source symbols are flattened and then forwarded to Shadow. This means FlattenShadows is only called on new combinations of source symbols. Unlike most other internal functions in Fusica LightFuse does not have the attribute HoldAll, which means the source symbols are evaluated here.*)
	LightFuse[symbols___] /; LightQ[symbols] := Shadow[symbols];
	LightFuse[symbols___] := Shadow @@ FlattenShadows[{symbols}];
	
	(*LightQ*)
	(*LightQ is used by LightFuse to immediately forward a set of symbols to Shadow, if there is an associated shadow symbol.*)
	SetUsage[LightQ, "LightQ[symbol$1, symbol$2, $$] returns True if there is a shadow symbol for the ordered set of source symbols symbol$1, symbol$2, $$, and False otherwise."];
	SetAttributes[LightQ, HoldAll];
	LightQ[___] = False;
	
	(*PrepareDefinitions*)
	SetUsage[PrepareDefinitions, "PrepareDefinitions[shadow$, symbol$, definitions$] rewrites the definition list definitions$ based on symbol$ so that it applies to shadow$."];
	(*PrepareDefinitions takes a definition list produce by Language`ExtendedDefinition and separates options and attributes, which can be assigned for the shadow without any transformations, and the ownvalues and all other values. On the latter two, InheritanceRule is used to transform them into definitions that can be used to assign values to the shadow symbol. The ownvalues are separated from all other values, because they need to be assigned after all other values have been set in the correct order. To get all definitions in the correct sequence they have to be evaluated twice in different orders, which makes it inconvenient to include the ownvalues in the same list. Any definitions that do not contain Substitute[shadow] in their lhs (which is possible through the use of Verbatim) are removed. If the shadow tag in the resulting definition is too deep then setting the definition will produce an error message, but otherwise the shadow symbol will still function properly.*)
	SetAttributes[PrepareDefinitions, HoldAll];
	PrepareDefinitions[
		shadow_Symbol,
		symbol_Symbol,
		Language`DefinitionList[
    		___,
    		HoldForm[symbol_Symbol] -> {
      			OwnValues 		-> ({ownvalues___} 		| ownvalue_),
      			SubValues 		-> ({subvalues___} 		| subvalue_),
      			UpValues 		-> ({upvalues___} 		| upvalue_),
      			DownValues 		-> ({downvalues___} 	| downvalue_),
      			NValues 		-> ({nvalues___} 		| nvalue_),
      			FormatValues 	-> ({formatvalues___} 	| formatvalue_),
      			DefaultValues 	-> ({defaultvalues___} 	| defaultvalue_),
      			Messages 		-> ({messages___} 		| message_),
      			Attributes 		-> ({attributes___} 	| attribute_)
      		},
    		___
    	]
   	] := Module[{options, defaults},
   
   		(*Extract options from default values*)
   		With[{input = Hold[defaultvalues, defaultvalue]},
    
    		(*Find position of options; insufficient if there are several options defaults (should not occur naturally)*)
    		With[{position = FirstPosition[input, _[Verbatim[HoldPattern][HoldPattern[Options[_]]], _], {}, 1]},
    			
    			(*Extract options*)
    			options = Hold @@ Extract[input, position, Hold][[;; , 2]];
    			
    			(*Remaining values are defaults*)
     			defaults = Delete[input, position]; 
	     
     		]
    
    	];
   
   		(*Return definitions*)
   		Join[
   			
   			{
   				
   				(*Options*)
	   			options,
	   			
	   			(*Attributes*)
	    		Hold[attributes, attribute]
	    		
	   		},
	   		
	   		(*Replace all symbols not protected by HoldPattern*)
    		ReplaceAll[
     
     			(*Remove definitions are expressly not intended for transfer to the shadow symbol*)
     			DeleteCases[
      
      				(*Create lists of values for shadow*)
      				Replace[
       					{
       						
       						(*All other values*)
        					Join[
         						Hold[
         							subvalues, 		subvalue, 
         							upvalues, 		upvalue, 
         							downvalues, 	downvalue, 
         							nvalues, 		nvalue, 
         							formatvalues, 	formatvalue
         						],
         						defaults,
         						Hold[messages, message]
         					],
         					
         					(*Ownvalues*)
        					Hold[ownvalues, ownvalue]
        					
        				},
       					InheritanceRule[shadow, symbol], {2}
       				],
      
      				expr_ /; FreeQ[Hold[expr], Substitute[shadow], Infinity],
      
      				{2}
      
      			],
     
     			Substitute[shadow] :> shadow
     
    		]
    		
   		]
   
   	];
	PrepareDefinitions[_Symbol, _Symbol, Language`DefinitionList[___]] = {Hold[], Hold[], Hold[], Hold[]};
	
	(*ReadableDefinitions*)
	SetUsage[ReadableDefinitions, "ReadableDefinitions[symbol$] is a function that returns a list of readable definitions for symbol$."];
	(*ReadableDefinitions simply removes the ReadProtected attribute from a symbol that has it, without also having the attribute Locked. It then calls Language`ExtendedDefinition, and scrubs its attributes and ownvalues using ScrubDefinitions. The condition checks in ReadableDefinitions are some of fairly time-consuming, and are hence formulated in such a way that they are not evaluated needlessly.*)
	SetAttributes[ReadableDefinitions, HoldAll];
	ReadableDefinitions[symbol_Symbol] /; MemberQ[Attributes[symbol], ReadProtected] /; FreeQ[Attributes[symbol], Locked] := Internal`InheritedBlock[{symbol},
		
		(*Remove ReadProtected attribute if possible*)
		ClearAttributes[symbol, ReadProtected];
	
		(*Return definitions for symbol without ownvalues and with scrubbed attributes*)
		ScrubDefinitions[symbol, Language`ExtendedDefinition[symbol]]
	
	];
	ReadableDefinitions[symbol_Symbol] := ScrubDefinitions[symbol, Language`ExtendedDefinition[symbol]];
	
	(*RemoveShadow*)
	(*This function is not accessible through any public-facing functions, and is intended only for developer use.*)
	SetUsage[RemoveShadow, "RemoveShadow[shadow$] removes shadow$ completely."];
	RemoveShadow::noshdw = "Argument `1` should be a valid shadow symbol created by Fuse.";
	RemoveShadow::rmlck = "Symbol `1` is Locked and cannot be removed.";
	RemoveShadow::rmptc = "Symbol `1` is Protected and cannot be removed.";
	RemoveShadow[shadow_Symbol ? ShadowQ] /; FreeQ[Attributes[shadow], Locked | Protected] := With[{light = Light[shadow]},
		
		(*Remove foundational definitions created by ResetShadow*)
		Unset[Light[shadow]];
		Unset @@ LightQ @@@ Hold[light];
		Unset @@ ResetShadow @@@ Hold[light];
		Unset @@ Shadow @@@ Hold[light];
		Unset[ShadowQ[shadow]];
		
		(*Remove cached definitions*)
		Unset @@ CachedDefinitions @@@ Hold[light];
		
		(*Remove memoized definitions for shadow*)
		ReleaseHold[Unset[InheritanceRule[shadow, #]] & /@ light];
		Unset @@ ReplacePart[Hold[ShadowFormat[shadow, light]], {1, 2, 0} -> List];
		Unset @@ ReplacePart[Hold[ShadowUsage[shadow, light]], {1, 2, 0} -> List];
		Unset @@ ReplacePart[Hold[Tracker[shadow, light]], {1, 2, 0} -> List];
		Unset @@ ReplacePart[Hold[Updater[shadow, light]], {1, 2, 0} -> List];
		
		(*Clear all definitions and remove symbol*)
		Remove[shadow];
				
	];
	RemoveShadow[shadow_Symbol ? ShadowQ] /; MemberQ[Attributes[shadow], Locked | Protected] := Null /; If[MemberQ[Attributes[shadow], Locked], Message[RemoveShadow::rmlck, HoldForm[shadow]], Message[RemoveShadow::rmptc, HoldForm[shadow]]];
	RemoveShadow[arg : Except[_Symbol ? ShadowQ]] := Null /; Message[RemoveShadow::noshdw, HoldForm[arg]];
		
	(*ResetShadow*)
	(*A functional shadow symbol requires Shadow, ShadowQ, Light, and LightQ to be set. These definitions are not associated to shadow, to minimize clutter in the user-intended definitions for shadow. When ResetShadow creates a new shadow symbol it does so using Unique in the context defined in Fusica`Settings`, and assigns the created shadow symbol as an ownvalue to Shadow[symbols] while setting LightQ[symbols] to True. If Shadow is called with symbols for which there is no defined ownvalue, checked with LightQ, a catch-all definition will call ResetShadow (through SetShadow) to define them. Shadow can be viewed as a memoized function to create shadow symbols. ResetShadow also sets ShadowQ to True for the shadow, and stores the source symbols associated to shadow as an ownvalue for Light. These are all used to flatten symbols given as input to Fuse, and for nothing else. If a shadow symbol already exists, ResetShadow simply runs Unprotect and ClearAll, effectively resetting it to a freshly created shadow symbol with no current definitions. ResetShadow is only called from inside SetShadow, to create or reset a shadow symbol for a given list of source symbols.*)
	SetUsage[ResetShadow, "ResetShadow[symbol$1, symbol$2, $$] clears the shadow symbol associated to the ordered set symbol$1, symbol$2, $$ if it exists, or creates it if it does not."];
	SetAttributes[ResetShadow, HoldAllComplete];
	ResetShadow[symbols__Symbol] := With[{shadow = Unique[Fusica`Settings`$ShadowContext <> "$"]},
		
		(*Store shadow symbol*)
		Shadow[symbols] = shadow;
		
		(*Set LightQ to True for source symbols*)
		LightQ[symbols] = True;
		
		(*Store source symbols for shadow*)
		Light[shadow] = Hold[symbols];
		
		(*Set ShadowQ to true for shadow*)
		ShadowQ[shadow] = True;
		
		(*Redefine ResetShadow to clear shadow*)
		With[{name = ShadowName[symbols] = Fusica`Settings`$ShadowContext <> SymbolName[shadow]},
			
			ResetShadow[symbols] := (  
				
				(*Unprotect shadow*)
				Unprotect[name]; 
				
				(*Clear all definitions*)
				ClearAll[name];
				
			);
				
		];
				
	];
	
	(*ScrubDefinitions*)
	SetUsage[ScrubDefinitions, "ScrubDefinitions[symbol$, definitions$] removes all ownvalues and excluded attributes for symbol$ contained in the definition list definitions$."];
	SetAttributes[ScrubDefinitions, HoldFirst];
	ScrubDefinitions[
		symbol_Symbol,
		Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {OwnValues -> Except[{}], rest__}, right___]
	] := ScrubDefinitions[symbol, Language`DefinitionList[left, HoldForm[symbol] -> {OwnValues -> {}, rest}, right]];
	ScrubDefinitions[
		symbol_Symbol,
		Language`DefinitionList[left___, HoldForm[symbol_Symbol] -> {rest__, Attributes -> (attributes : {___, Locked | Protected | Stub | Temporary, ___})}, right___]
	] := With[{scrubbed = DeleteCases[attributes, Locked | Protected | Stub | Temporary]},
	
		ScrubDefinitions[symbol, Language`DefinitionList[left, HoldForm[symbol] -> {rest, Attributes -> scrubbed}, right]]
		
	];
	ScrubDefinitions[_Symbol, definitions_] := definitions;
	
	(*SetDefinitions*)
	SetUsage[SetDefinitions, "SetDefinitions[shadow$, symbols$, definitions$] copies to shadow$ all definitions associated to symbols$ in the definition list definitions$."];
	(*SetDefinitions calls PrepareDefinitions to obtain the definitions for shadow given a set of source symbols. These definitions are set directly in the case of attributes and options, where some care is taken to prevent premature evaluation. The non-scrubbed attributes of the source symbols are also checked for mismatches, which will trigger a warning message. Since the ReadProtected attribute has to be removed before Language`ExtendedDefinition can be called, the ReadProtected attribute is checked for in the original source symbols as well, and set for the shadow if present. All definitions are evaluated twice to ensure that they end up in the exact same order as the original definitions. Ownvalue definitions must be set last, because they will interfere with the other definitions otherwise.*)
	SetAttributes[SetDefinitions, HoldAll];
	SetDefinitions[head : CopyTo | Fuse, shadow_Symbol, {symbols__Symbol}] := SetDefinitions[head, shadow, {symbols}, Thread[ReadableDefinitions[{symbols}]]]; 
	SetDefinitions[head : CopyTo | Fuse, shadow_Symbol, {symbols__Symbol}, definitions_List] := Module[{options, attributes = Attributes[{symbols}], othervalues, ownvalues},
   
   		(*Give a warning when attributes mismatch*)
		If[! SameQ @@ DeleteCases[attributes, Locked | Protected | ReadProtected | Stub | Temporary, {2}], 
					
			Message[head::attrmm, StringRiffle[List @@ SymbolName /@ Unevaluated /@ Hold[symbols], ", "]]
			
		];
		
		(*Make shadow ReadProtected if necessary*)
		If[MemberQ[attributes, ReadProtected, {2}], SetAttributes[shadow, ReadProtected]];
		      
		(*Add aliasing for kernel symbols and prepare definitions for assignment*)
		With[{full = Thread[AddKernelCodeAliasing[head, {symbols}, definitions]]},      	
		
				{options, attributes, othervalues, ownvalues} = Transpose[Thread[PrepareDefinitions[shadow, {symbols}, full]]]
				
		];
      
      	(*Force the use of cached definitions to prevent infinite recursions in the case of cyclical dependencies*)
      	Block[{$Tracker},
	      
	   		(*Set options*)
			With[{a1 = Sequence @@@ Join @@ options}, 
	    	
	    		If[a1 =!= Hold[],
	    		
		    		With[{a2 = Unevaluated @@ List @@@ Hold[a1]}, 
		     	
		     			Options[shadow] = a2
		     	
		     		]
		     		
	    		];
	     	
	     	];
	   
	   		(*Set attributes*)
			With[{a1 = Join @@ attributes}, 
	    		
	    		With[{a2 = Unevaluated @@ List @@@ Hold[a1]}, 
	     			
	     			SetAttributes[shadow, a2]
	     			
	     		]
	     		
	     	];
	   	
	   		(*Set remaining values*)
	     	CompoundExpression @@ Join @@ Join[
	     		
	     		(*First set all values except ownvalues*)
	     		othervalues, 
	     		Reverse[Most[othervalues]], 
	     		
	     		(*Set ownvalues*)
	     		ownvalues, 
	     		Reverse[Most[ownvalues]]
	     	
	     	];
	     	
      	];
	     	
   	]; 
	
	(*SetShadow*)
	(*SetShadow is the main function behind Fuse that calls ResetShadow to create an empty shadow symbol, and then uses SetDefinitions to assign it the combined definitions of the source symbols. SetShadow is protected from aborts because it is directly modifying the definitions of shadow, which may produce a corrupted shadow symbol if it is interrupted at an inopportune time. SetShadow also takes care of all the cosmetic definitions of the shadow symbol, such as its usage message (using ShadowUsage) and formatting (using ShadowFormat), sets the auto-updating ownvalue based on Tracker, and stores the cached definitions of the shadow symbol. The formatting behavior of shadow symbols is set before SetDefinitions is called, so it can be overwritten. The usage message and Tracker are set after SetDefinitions is called, so they overwrite any fused definitions. To handle the case where ownvalues are combined as well (currently not available user-side without modifying the package), there is a check to verify that the tracker ownvalue is not shadowed by any fused ownvalues. SetShadow is called directly by a shadow symbol if updating is required; it will not go through Fuse or LightFuse again.*)
	SetUsage[SetShadow, "SetShadow[symbols$, definitions$] returns a temporary shadow symbol associated to symbols$ whose definition is generated from the values, options, and attributes in definitions$."];
	SetAttributes[SetShadow, HoldAll];
	SetShadow[{symbols__Symbol}] := With[{definitions = Thread[ReadableDefinitions[{symbols}]]}, 

			SetShadow[{symbols}, definitions]
			
	];
	SetShadow[{symbols__Symbol}, definitions_] := ReleaseHold[
	
		AbortProtect[
		
			(*Clear the existing shadow symbol, or create one if there is none*)
			ResetShadow[symbols];
			
			(*Create new definitions for the shadow symbol*)
			With[{shadow = Shadow[symbols]},
				
				(*Set default formatting behavior*)
				shadow /: MakeBoxes[HoldPattern[shadow], _] = ShadowFormat[shadow, {symbols}];
		
				(*Create definitions for shadow from symbols*)
				SetDefinitions[Fuse, shadow, {symbols}, definitions];

				(*Overwrite usage message*)
				shadow::usage = ShadowUsage[shadow, {symbols}];
			   	
				(*Enable updating functionality in lieu of user accessible tracked symbol functionality*)
				With[{tracker = Tracker[shadow, {symbols}]},
		
					(*Add tracker ownvalue to shadow*)
					PrependTo[OwnValues[shadow], tracker];
					
					(*Check for masking ownvalues for shadow*)
					If[
						
						First[OwnValues[shadow]] =!= tracker, 
						
						Message[
							Fuse::trackfail, 
							First[OwnValues[shadow]], 
							StringRiffle[List @@ SymbolName /@ Unevaluated /@ Hold[symbols], ", "]
						]
						
					];
					
				];
				
				(*Overload Update to allow manual updating of cached definitions*)
				PrependTo[UpValues[shadow], Updater[shadow, {symbols}]];
				
				(*Cache definitions for UpdateCacheQ*)
				CachedDefinitions[shadow] = definitions;
				
				(*Set shadow attributes*)
				SetAttributes[shadow, {Protected, ReadProtected, Temporary}];
				
				(*Return shadow*)
				Hold[shadow]
				
			]
		
		]
			    			
	];
		
	(*Shadow*)
	(*If Shadow is called with symbols for which there is no defined ownvalue, the catch-all definition will call ShadowName (through SetShadow and ResetShadow) to define one. SetShadow then sets Shadow[symbols] to shadow, so Shadow can be viewed as a memoized function to create shadow symbols.*)
	SetUsage[Shadow, "Shadow[symbol$1, symbol$2, $$] creates or returns the shadow symbol associated to the ordered set symbol$1, symbol$2, $$"];
	SetAttributes[Shadow, HoldAll];
	Shadow[symbols__Symbol] := SetShadow[{symbols}];
	
	(*ShadowFormat*)
	SetUsage[ShadowFormat, "ShadowFormat[shadow$, symbols$] generates an InterpretationBox to represent shadow$."];
	SetAttributes[ShadowFormat, HoldAll];
	ShadowFormat[shadow_Symbol, {symbols__Symbol}] := ShadowFormat[shadow, {symbols}] = With[
		{
			boxes = Fusica`Settings`$ShadowBoxes[symbols]
		}, 
		
		InterpretationBox[
			StyleBox[boxes, "NonInterpretableSummary"], 
			shadow, 
			Selectable -> False, Editable -> False, SelectWithContents -> True
		]
	
	];

	(*ShadowName*)
	SetUsage[ShadowName, "ShadowName[symbol$1, symbol$2, $$] returns the name of the shadow symbol associated to symbol$1, symbol$2, $$"];
	SetAttributes[ShadowName, HoldAll];
	
	(*ShadowQ*)
	SetUsage[ShadowQ, "ShadowQ[symbol$] returns True if symbol$ is a shadow, and False otherwise."];
	SetAttributes[ShadowQ, HoldFirst];
	ShadowQ[_] = False;
	
	(*ShadowUsage*)
	SetUsage[ShadowUsage, "ShadowUsage[shadow$, symbols$] generates a usage message for shadow$."];
	SetAttributes[ShadowUsage, HoldAll];
	ShadowUsage[shadow_Symbol, {symbols__Symbol}] := ShadowUsage[shadow, {symbols}] = StringJoin[
		ShadowName[symbols], 
		" is the shadow symbol generated by Fuse[", 
		StringRiffle[List @@ SymbolName /@ Unevaluated /@ Hold[symbols], ", "],
		"]. This symbol is intended for internal use only, and should not be modified."
	];
	
	(*Substitute*)
	SetUsage[Substitute, "Substitute[shadow$] is an inert function used for secure replacements."];
	SetAttributes[Substitute, {HoldFirst, Protected}];
	
	(*Tracker*)
	SetUsage[Tracker, "Tracker[shadow$, symbols$] generates an ownvalue for shadow$ to detect changes to symbols$."];
	SetAttributes[Tracker, HoldAll];
	(*Tracker generates the ownvalue for a shadow symbol that runs SetShadow whenever the cached definitions (stored in CachedDefinitions) differ from the currently available definitions. The Tracker ownvalue will always check $Tracker first to prevent unnecessary evaluations of the time-consuming ReadableDefinitions function.*)
	Tracker[shadow_Symbol, {symbols__Symbol}] := Tracker[shadow, {symbols}] = RuleDelayed[
						
		HoldPattern[HoldPattern[shadow] /; $Tracker], 
		
		With[{definitions = Thread[ReadableDefinitions[{symbols}]]}, 

			SetShadow[{symbols}, definitions] /; CachedDefinitions[shadow] =!= definitions

		]
		
	];
	
	(*Updater*)
	SetUsage[Updater, "Updater[shadow$, symbols$] generates an upvalue for Update[shadow$] to force manual updating of the definitions of shadow$."];
	(*Updater generates the upvalue for Update[shadow] that runs SetShadow regardless of the value of $Tracker or the differences between the current and cached definitions of the source symbols. Update is overloaded in a way that the standard functionality of Update is not impeded.*)
	SetAttributes[Updater, HoldAll];
	Updater[shadow_Symbol, {symbols__Symbol}] := Updater[shadow, {symbols}] = RuleDelayed[
						
		HoldPattern[Update[HoldPattern[shadow]] /; $Update], 
		
		(
			Block[{Fusica`Private`$Update}, Update[Unevaluated[shadow]]];
			SetShadow[{symbols}];
		)
		
	];
	
	(*ValidArguments*)
	SetUsage[ValidArguments, "ValidArguments[arg$1, arg$2, $$] returns True if all arg$1, arg$2, $$ evaluate to symbols, and produces a message if they do not."];
	(*ValidArguments, like LightFuse, does not have attribute HoldAll, allowing the arguments of Fuse to be evaluated here. Any Fuse symbols occurring in the call to Fuse are replaced with ValidArgument symbols by the Block within which ValidArguments is always called, so that these Fuse occurrences reduce to True if the arguments to that nested Fuse symbol are symbols, but the Fuse occurrence remains an unevaluated ValidArguments expression if they are not. Only the first symbols in the top level and nested Fuse occurrences trigger a message; invalid Fuse arguments themselves do not. Since ValidArguments produces True in the case of symbol arguments, and since True is itself a symbol, ValidArguments will return True if the entire Fuse pattern is valid.*)
	ValidArguments[__Symbol] = True;
	ValidArguments[(_Symbol | _ValidArguments) ..., exception : Except[_Symbol | _ValidArguments], ___] := Null /; Message[Fuse::ssym, HoldForm[exception]];
	
	
	(*Public definitions*)
	
	(*$Tracker*)
	$Tracker = True;
	
	(*CopyTo*)
	CopyTo[target_Symbol /; FreeQ[Attributes[target], Locked | Protected]] := CopyTo[target, target];
 	CopyTo[target_Symbol /; FreeQ[Attributes[target], Locked | Protected], {}] := ClearAll[target];
 	CopyTo[target_Symbol /; FreeQ[Attributes[target], Locked | Protected], symbol_Symbol | {symbols__Symbol}] := AbortProtect[
 		
 		Block[{$Tracker},
 		
	 		With[{source = FlattenShadows[{symbol, symbols}]}, 
	 			
	 			With[{definitions = Thread[ReadableDefinitions[{##}]] & @@ source},
	 				
			 		(*Clear the target symbol*)
			 		ClearAll[target];
			 		
			 		(*Copy the definitions of the source symbols*)
			 		SetDefinitions[CopyTo, target, {##}, definitions] & @@ source;
			 		
			 		(*If all source symbols have identical SyntaxInformation*)
			 		If[SameQ @@ SyntaxInformation /@ Unevaluated /@ source, 
			 			
			 			(*Copy SyntaxInformation*)	
						With[{syntax = Extract[source, 1, Unevaluated]}, 
							
							If[SyntaxInformation[syntax] != {}, SyntaxInformation[Unevaluated[target]] = SyntaxInformation[syntax]]
							
						]
			 				
			 		]
			 		
	 			]
		 		
	 		]
	 		
 		];
	 		
 	];
 	CopyTo[target_Symbol /; With[{attributes = Attributes[target]}, MemberQ[attributes, Protected] && FreeQ[attributes, Locked]], RepeatedNull[_Symbol | {___Symbol}, 1]] := Null /; Message[CopyTo::wrsym, HoldForm[target]]; 
 	CopyTo[target_Symbol /; MemberQ[Attributes[target], Locked], RepeatedNull[_Symbol | {___Symbol}, 1]] := Null /; Message[CopyTo::locked, HoldForm[target]];
 	CopyTo[_Symbol, Except[_Symbol | {___Symbol}]] := Null /; Message[CopyTo::lsym, 2, 2];
 	CopyTo[exception : Except[_Symbol], RepeatedNull[_, 1]] := Null /; Message[CopyTo::ssym, HoldForm[exception]];
	
	(*Fuse*)
	(*Fuse forwards its arguments to LightFuse, provided that they evaluate to symbols (as checked through ValidArguments). Fuse has attribute HoldAllComplete to allow evaluation of the arguments in a Block with $Tracker = True, preventing unnecessary definition updates. (At this point we are only interested in the shadow values to which they evaluate, not that these shadow values have up-to-date definitions.) The definition as it is here allows Fuse to handle infinite recursions (f := Fuse[f]; f) somewhat elegantly, i.e., with only one error message before returning unevaluated. Still, shadows are evaluated twice in assignments (a = Fuse[b]) and messages are duplicated in assignments (a = Fuse[3]) because of Block; I have not yet found a way around this.*)
	p : Fuse[args__] := Block[{$Tracker}, LightFuse[args]] /; Block[{$Tracker, Fuse = ValidArguments}, p];
	
	(*FusePattern*)
	FusePattern[pattern___] := HoldPattern[s_Symbol ? ShadowQ /; MatchQ[Light[s], Verbatim[Hold][pattern]]];
	
	
	(*Aliasing*)
	
	(*Diamond*)
	With[{alias = Fusica`Settings`$Alias},
		
		With[{attributes = Attributes[alias]},
		
			If[FreeQ[attributes, Protected] && !ValueQ[alias],
				
				alias = Fuse;
				
				If[FreeQ[attributes, Locked], Protect[alias]]
				
			]
			
		]
		
	];
	
	
(*End private context*)
End[];


(*Bulletproofing*)
SetAttributes[$Tracker, Protected];
SetAttributes[CopyTo, {HoldFirst, Protected, ReadProtected}];
SetAttributes[Fuse, {HoldAllComplete, Protected, ReadProtected}];
SetAttributes[FusePattern, {Protected, ReadProtected}];
	

(*End fusica package*)
EndPackage[];