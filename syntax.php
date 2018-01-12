<?php
$predicateSettings=false;

function hasStrayChars($s) {
    global $predicateSettings;
    if ($predicateSettings) {
       if (mb_ereg_match('.*[^A-Za-z∀∃=¬∨∧↔→⊥\s\)\(\]\[\}\{]', $s)) {
          return true;
       } 
    } else {
       if (mb_ereg_match('.*[^A-Z¬∨∧↔→⊥\s\)\(\]\[\}\{]', $s)) {
          return true;
       } 
    }
    return false;
}
                                         
function regularizeMe($s) {
    $s=mb_ereg_replace('\[','(',$s);
    $s=mb_ereg_replace('\{','(',$s);
    $s=mb_ereg_replace('\]',')',$s);
    $s=mb_ereg_replace('\}',')',$s);
    $s=mb_ereg_replace('\s','',$s);
    return $s;
}

function listUnion($z,$x) {
   return array_unique(array_merge($z, $x));
}                                

function wffToStringAndDepth($w) {
    global $predicateSettings;
    $rv = new StdClass();
    $rv->str = '';
    $rv->depth = 0;
    if ($w->wffType == "splat") {
        $rv->str = '⊥';
        return $rv;
    }
    if ($w->wffType == "identity") {
       $rv->str = $w->myTerms[0] . ' = ' . $w->myTerms[1];
       return $rv;
    }
    if ($w->wffType == "atomic") {
       $rv->str = $w->myLetter;
       if ($predicateSettings) {
          $rv->str .= implode($w->myTerms);
       } 
       return $rv;
    }
    $rightResult = wffToStringAndDepth($w->rightSide);
    $rightAdd = $rightResult->str;
    $rightDepth = $rightResult->depth;
    if (isBinOp($w->rightSide->mainOp)) {
        switch ($rightDepth % 2) {
            case 0:
                $rightAdd='(' . $rightAdd . ')';
                break;
            case 1:
                $rightAdd='[' . $rightAdd . ']';
                break;
        }
        $rightDepth += 1;
    }
    if ($w->wffType == "quantified") {
       $rv->str = $w->mainOp . $w->myLetter . $rightAdd;      
       $rv->depth=$rightDepth;
       return $rv;
    }
    if ($w->mainOp == "¬") {
        $rv->str = "¬" . $rightAdd;
        $rv->depth = $rightDepth;
        return $rv;
    }
    $leftResult=wffToStringAndDepth($w->leftSide);
    $leftAdd=$leftResult->str;
    $leftDepth=$leftResult->depth;
    if (isBinOp($w->leftSide->mainOp)) {
        switch($leftDepth % 2) {
            case 0:
                $leftAdd='(' . $leftAdd . ')';
                break;
            case 1:
                $leftAdd='[' . $leftAdd . ']';
                break;
        }
        $leftDepth += 1;
    }
    $rv->depth = max($rightDepth,$leftDepth);
    $rv->str = $leftAdd . " " . $w->mainOp . " " . $rightAdd;
    return $rv;
}

function wffToString($w) {
   return wffToStringAndDepth($w)->str;
}

function isBinOp($ch) {
    if (($ch=='→') || ($ch=='∨') || ($ch=='∧') || ($ch=='↔')) {
        return true;
    }
    return false;
}

function isMonOp($ch) {
    return (($ch=="¬") || ($ch=="∀") || ($ch=="∃"));
}

function isOp($ch) {
    return ((isBinOp($ch))||(isMonOp($ch)));
}

function isQuantifier($ch) {
    return (($ch=="∀") || ($ch=="∃"));
}

function isVar($ch) {
    return (($ch=="x") || ($ch=="y") || ($ch=="z"));
}

function getStLtrs($w) {
    $mL=array();
    if ($w->wffType == "splat") {
        return $mL;
    }
    if ($w->wffType == "atomic") {
       $mL=array($w->myLetter);
       return $mL;
    }
    if (w.mainOp=="¬") {
        $mL=getStLtrs($w->rightSide);
        return $mL;
    }
    $mL = getStLtrs($w->leftSide);
    $x = getStLtrs($w->rightSide);
    $mL = listUnion($mL, $x);
    return mL;
}

function newSLWff() {
   $w = new StdClass();
   $w->isWellFormed = true;
   $w->ErrMsg = "none";
   $w->wffType = 'unknown';
   $w->mainOp = '?';
   $w->myLetter = '';
   $w->leftSide = new StdClass();
   $w->rightSide = new StdClass();
   return $w;
}

function newPLWff() {
   $w = newSLWff();
   $w->myTerms = array();
   $w->allFreeVars = array();
   return $w;
}

// parse string to formula
function parseIt($s) {
   
    // initialize return formula   
    global $predicateSettings;
    if ($predicateSettings) {
       $wff = newPLWff();
    } else {
       $wff = newSLWff();
    }
    $mainOpPos = 0;
    $depthArray=array();
    $s=regularizeMe($s);
   
    // Check if non-empty 
    if ($s=='') {
        $wff->isWellFormed=false;
        $wff->ErrMsg="Formula or subformula is blank.";
        return $wff;
    }
   
   // check for stray characters
    if (hasStrayChars($s)) {
       $wff->isWellFormed=false;
       if ($predicateSettings) {
          $wff->ErrMsg="Input field contains characters or punctuation not allowed in the language of FOL. A statement should contain only parentheses ( [ { } ] ), predicates A–Z and =, terms a–w, variables x–z, the contradiction symbol ⊥, and the operators ¬, ∨, ∧, →, ↔, ∃, ∀ (or their alternatives).";
       } else {
          $wff->ErrMsg="Input field contains characters or punctuation not allowed in the language of TFL. A statement should contain only parentheses ( [ { } ] ), statement letters A–Z, the contradiction symbol ⊥, and the operators ¬, ∨, ∧, →, and ↔ (or their alternatives).";
       }
       return $wff;
    }

   // Check depths and parentheses balance
   $d=0;
   for ($i=0; $i<mb_strlen($s); $i++) {
      $c = mb_substr($s, $i, 1);
      if ($c == '(') {
         $d++;
      }
      if ($c == ')') {
         $d -= 1;
      }
      array_push($depthArray, $d);
   }
   if ($depthArray[(count($depthArray) - 1)] != 0) {
      $wff->isWellFormed = false;
      $wff->ErrMsg = "Parentheses are unbalanced.";
      return $wff;
   }
   
   // remove matching outermost parentheses
   if ($depthArray[0]==1) {
      $theyMatch=true;
      for ($i=1; $i<(count($depthArray) -1); $i++) {
         $theyMatch=(($theyMatch) && ($depthArray[$i] > 0));
      }
      if ($theyMatch) {
         return parseIt(mb_substr($s, 1, (mb_strlen($s) - 2) ) ); 
      }
   }
   
    // check if in atomic family
    if (!( mb_ereg_match('.*[¬∧∨→↔∀∃]', $s) )) {
       // should be in atomic family
       
       // should not contain parentheses
       if (mb_ereg_match('.*[\(\)]', $s) ) {
          $wff->isWellFormed = false;
          $wff->ErrMsg = "Misplaced parentheses.";
          return $wff;
       }
       
       // check if splat 
       if ($s=="⊥") {
          $wff->wffType="splat";
          return $wff;
       }
       
       // if still contains splat, that is no good
       if ( mb_ereg_match('.*⊥', $s) ) {
          $wff->isWellFormed = false;
          $wff->ErrMsg = "Formula contains ⊥ but not in isolation.";
          return $wff;
       }
       
       // check for identity statement
       if ( mb_ereg_match('.*=', $s) ) {
          if ( mb_ereg_match('[a-z]=[a-z]$', $s) ) {
             $wff->wffType = 'identity';
             $wff->myTerms = explode('=',$s);
             $wff->allFreeVars = array();
             if (isVar($wff->myTerms[0])) {
                array_push($wff->allFreeVars, $wff->myTerms[0]);
             }
             if ((isVar($wff->myTerms[1])) && ($wff->myTerms[1] != $wff->myTerms[0])) {
                array_push($wff->allFreeVars, $wff->myTerms[1]);
             }
             return $wff;
          } else {
             $wff->isWellFormed = false;
             $wff->ErrMsg = "Poorly formed identity statement. Identity statement should be of the form <var>t</var> = <var>s</var>.";
             return $wff;
          }
       }
       
       // check for sentential atomic
       if (!($predicateSettings)) {
          if ( mb_ereg_match('[A-Z]$', $s) ) {
             $wff->wffType = "atomic";
             $wff->myLetter = $s;
             return $wff;
          } else {
             $wff->isWellFormed = false;
             $wff->ErrMsg = "Poorly formed atomic statement. In TFL, an atomic statement should be a single statement letter.";
             return $wff;
          }
       }
       
       // should be predicate atomic
       if (!( mb_ereg_match('[A-Z]', $s) )) {
          $wff->isWellFormed = false;
          $wff->ErrMsg = "An atomic formula must begin with a predicate.";
          return $wff;
       }
       if (mb_strlen($s) == 1) {
          $wff->isWellFormed = false;
          $wff->ErrMsg = "An atomic formula must have terms, not just a predicate.";
          return $wff;
       }
       if (mb_ereg_match('..*[A-Z]', $s)) {
          $wff->isWellFormed=false;
          $wff->ErrMsg="Predicates may only appear at the beginning of an atomic formula.";
          return $wff;
       }
       if (mb_ereg_match('..*[^a-z]', $s)) {
          $wff->isWellFormed=false;
          $wff->ErrMsg="An atomic formula should contain only predicates followed by terms.";
          return $wff;
       }
       $wff->wffType='atomic';
       $wff->myLetter=substr($s, 0 , 1);
       $wff->myTerms=str_split(substr($s, 1));
       $wff->allFreeVars = array();
       foreach ($wff->myTerms as $t) {
          if (isVar($t)) {
             array_push($wff->allFreeVars, $t);
          }
       }
       $wff->allFreeVars = array_unique($wff->allFreeVars);
       return $wff;
    }       

   // find main operator 
   for ($i=0; $i<mb_strlen($s); $i++) {
      $c = mb_substr($s, $i, 1);
      if ((isOp($c)) && ($depthArray[$i]==0)) {
         if ($wff->mainOp=='?') {
            $wff->mainOp=$c;
            $mainOpPos=$i;
         } else {
            if ((isBinOp($wff->mainOp)) && (isBinOp($c))) {
               $wff->isWellFormed=false;
               $wff->ErrMsg="Too many operators or too few parentheses to disambiguate.";
               return $wff;
            } else {
               if ((isMonOp($wff->mainOp)) && (isBinOp($c))) {
                  $wff->mainOp=$c;
                  $mainOpPos=$i;
               }
            }
         }
      }
   }

   // if no operator found, return an error 
   if ($wff->mainOp=='?') {
      $wff->isWellFormed=false;
      $wff->ErrMsg="Missing connective/operator or misplaced parentheses.";
      return $wff;
   }
   
   // quantified wff
   if (isQuantifier($wff->mainOp)) {
      $wff->wffType="quantified";
      // quantifier must come first 
      if ($mainOpPos != 0) {
         $wff->isWellFormed=false;
         $wff->ErrMsg="Misuse of a quantifier internally in a formula.";
         return $wff;
      }
      // variable must be next 
      if (!(isVar( mb_substr($s, 1, 1) ))) {
         $wff->isWellFormed=false;
         $wff->ErrMsg="A quantifier is used without binding a variable.";
      }
      $wff->myLetter=mb_substr($s, 1, 1);

      // what comes after quantifier must be well-formed 
      $wff->rightSide=parseIt(mb_substr($s, 2));
      if (!($wff->rightSide->isWellFormed)) {
         $wff->isWellFormed=false;
         $wff->ErrMsg=$wff->rightSide->ErrMsg;
         return $wff;
      }
      // terms are same as right side except possibly adding bound variable
      $wff->myTerms=$wff->rightSide->myTerms;
      if (!(in_array($wff->myLetter, $wff->myTerms))) {
         array_push($wff->myTerms, $wff->myLetter);
      }
      // free variables are the same minus the one being bound
      $wff->allFreeVars = array();
      foreach ($wff->rightSide->allFreeVars as $v) {
         if ($v != $wff->myLetter) {
            array_push($wff->allFreeVars, $v);
         }
      }
      return $wff;
   }

   $wff->wffType="molecular";
   
   // negation
   if ($wff->mainOp == "¬") {
      // negation must be at start if main op
      if ($mainOpPos != 0) {
         $wff->isWellFormed=false;
         $wff->ErrMsg="Misuse of negation internally in formula.";
         return $wff;
      }
      // parse negated formula
      $wff->rightSide=parseIt( mb_substr($s, 1) );
      if (!($wff->rightSide->isWellFormed)) {
         $wff->isWellFormed=false;
         $wff->ErrMsg=$wff->rightSide->ErrMsg;
         return $wff;
      }
      if ($predicateSettings) {
         $wff->myTerms=$wff->rightSide->myTerms;
         $wff->allFreeVars=$wff->rightSide->allFreeVars;
      }
      return $wff;
   }
   
   // binary molecular
   $wff->leftSide = parseIt(mb_substr($s, 0, $mainOpPos));
   if (!($wff->leftSide->isWellFormed)) {
      $wff->isWellFormed=false;
      $wff->ErrMsg = $wff->leftSide->ErrMsg;
      return $wff;
   }
   
   $wff->rightSide = parseIt(mb_substr($s, $mainOpPos + 1));
   if (!($wff->rightSide->isWellFormed)) {
      $wff->isWellFormed=false;
      $wff->ErrMsg=$wff->rightSide->ErrMsg;
      return $wff;
   }
   
   if ($predicateSettings) {
      $wff->myTerms = listUnion($wff->leftSide->myTerms, $wff->rightSide->myTerms);
      $wff->allFreeVars = listUnion($wff->leftSide->allFreeVars, $wff->rightSide->allFreeVars);
   }
   return $wff;
}

function subTerm($w, $n, $v) {
    if (!(in_array($v, $w->allFreeVars))) {
        return clone $w;
    }
    $x = newPLWff();
    $x->wffType=$w->wffType;
    $x->mainOp=$w->mainOp;
    $x->myLetter=$w->myLetter;
    $x->allFreeVars = array();
    foreach ($w->allFreeVars as $nv) {
       if ($nv != $v) {
          array_push($x->allFreeVars, $nv);
       }
    }

   if (($w->wffType=="atomic") || ($w->wffType=="identity")) {
      $x->myTerms = array();
      foreach ($w->myTerms as $t) {
         if ($t == $v) {
            array_push($x->myTerms, $n);
         } else {
            array_push($x->myTerms, $t);
         }
      }
      return $x;
   }

   $x->rightSide=subTerm($w->rightSide,$n,$v);

   $x->myTerms=$x->rightSide->myTerms;

   if (isMonOp($x->mainOp)) {
      return $x;
   }
   $x->leftSide=subTerm($w->leftSide,$n,$v);
   $x->myTerms=listUnion($x->myTerms, $x->leftSide->myTerms);

   return $x;
}

function sameWff($a, $b) {
   global $predicateSettings;
   if ($a->wffType != $b->wffType) {
      return false;
   }
   if ($a->wffType == "splat") {
      return true;
   }
   if ($a->wffType == "identity") {
      return (($a->myTerms[0] == $b->myTerms[0]) && ($a->myTerms[1] == $b->myTerms[1]));
   }
   if ($a->wffType == "atomic") {
      if ($predicateSettings) {
         if ($a->myLetter != $b->myLetter) {
            return false;
         }
         if (count($a->myTerms) != count($b->myTerms)) {
            return false;
         }
         for ($i = 0; $i<count($a->myTerms); $i++) {
            if ($a->myTerms[$i] != $b->myTerms[$i]) {
               return false;
            }
         }
         return true;
      } else {
         return ($a->myLetter == $b->myLetter);
      }
   }
   if ($a->mainOp != $b->mainOp) {
      return false;
   }
   if ((isQuantifier($a->mainOp)) && ($a->myLetter != $b->myLetter)) {
      return false;
   }
   if (isMonOp($a->mainOp)) {
      return sameWff($a->rightSide, $b->rightSide);
   }
   return ( (sameWff($a->leftSide, $b->leftSide)) && (sameWff($a->rightSide, $b->rightSide)) );
}

?>
