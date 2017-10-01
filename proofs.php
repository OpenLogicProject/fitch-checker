<?php

$tfl_rules = array('∧I','∧E','⊥I','⊥E','¬I','¬E','→I','→E','TND','∨I','∨E','↔I','↔E','DS','R','MT','DNE','DeM','Pr','Hyp','X','IP','LEM');
$fol_rules = array('∀E','∀I','∃I','∃E','=I','=E','CQ');

$cite_nums = array(
   "∧I" => array(2, 0),
   "∧E" => array(1, 0),
   "⊥I" => array(2, 0),
   "⊥E" => array(1, 0),
   "¬I" => array(0, 1),
   "¬E" => array(2, 0),
   "→I" => array(0, 1),
   "→E" => array(2, 0),
   "TND" => array(0, 2),
   "∨I" => array(1, 0),
   "∨E" => array(1, 2),
   "↔I" => array(0, 2),
   "↔E" => array(2, 0),
   "DS" => array(2, 0),
   "R" => array(1, 0),
   "MT" => array(2, 0),
   "DNE" => array(1, 0),
   "DeM" => array(1, 0),
   "∀E" => array(1, 0),
   "∀I" => array(1, 0),
   "∃I" => array(1, 0),
   "∃E" => array(1, 1),
   "=I" => array(0, 0),
   "=E" => array(2, 0),
   "CQ" => array(1, 0),
   "Hyp" => array(0,0),
   "Pr" => array(0,0),
   "X" => array(1, 0),
   "IP" => array(0, 1),
   "LEM" => array(0, 2)
);

function followsByCQThisWay($a, $b) {
   return (
      ($a->mainOp == "¬")
      &&
      ($b->rightSide->mainOp == "¬")
      &&
      ( 
         (($a->rightSide->mainOp == "∀") && ($b->mainOp == "∃"))
         ||
         (($a->rightSide->mainOp == "∃") && ($b->mainOp == "∀"))
      )
      &&
      ($b->myLetter == $a->rightSide->myLetter)
      &&
      (sameWff($a->rightSide->rightSide, $b->rightSide->rightSide))
   );
}

function followsByCQ($a, $b) {
   return (
      (followsByCQThisWay($a, $b))
      ||
      (followsByCQThisWay($b, $a))
   );
}

function isSelfId($w) {
   return (
      ($w->wffType == "identity")
      &&
      (!(isVar($w->myTerms[0])))
      &&
      ($w->myTerms[0] == $w->myTerms[1])
   );
}

function followsByLLThisWay($c, $a, $b) {
   return (
      ($a->wffType == "identity") &&
      (
         (differsBySwappingFor($c, $b, $a->myTerms[0], $a->myTerms[1]))
         ||
         (differsBySwappingFor($c, $b, $a->myTerms[1], $a->myTerms[0]))
      )
   );
}

function differsBySwappingFor($q, $p, $s, $t) {
   if ($p->wffType != $q->wffType) {
      return false;
   }
   if ($p->wffType == "splat") {
      return true;
   }
   if (($p->wffType == "atomic") || ($p->wffType == "identity")) {
      if (count($p->myTerms) != count($q->myTerms)) {
         return false;
      }
      if (($p->wffType == "atomic") && ($p->myLetter != $q->myLetter)) {
         return false;
      }
      for ($i=0; $i<count($p->myTerms); $i++) {
         if (
               ($p->myTerms[$i] != $q->myTerms[$i])
               &&
               (!(
                  ($p->myTerms[$i] == $t)
                  &&
                  ($q->myTerms[$i] == $s)
               ))
            ) {
            return false;
         }
      }
      return true;
   }
   if ($p->mainOp != $q->mainOp) {
      return false;
   }
   if (isMonOp($p->mainOp)) {
         return differsBySwappingFor($q->rightSide, $p->rightSide, $s, $t);
   }
   return (
         (differsBySwappingFor($q->rightSide, $p->rightSide, $s, $t))
      &&
         (differsBySwappingFor($q->leftSide, $p->leftSide, $s, $t))
      );
}


function followsByLL($c, $a, $b) {
   return (
      (followsByLLThisWay($c, $a, $b)) ||
      (followsByLLThisWay($c, $b, $a))
   );
}


function followsByEG($c, $a) {
   if (!($c->mainOp == "∃")) {
      return false;
   }
   
   // vacuous instance
   if (!(in_array($c->myLetter, $c->rightSide->allFreeVars))) {
      return (sameWff($c->rightSide, $a));
   }
       
   // regular instance
   // no double binding unless vacuous
   if (in_array($c->myLetter, $a->myTerms))  {
      return false;
   }
   
   foreach ($a->myTerms as $t) {
      if (!(isVar($t))) {
         if (sameWff($a, subTerm($c->rightSide, $t, $c->myLetter))) {
            return true;
         }
      }
   }
   return false;
}

function followsByUI($c, $a) {
   if (!($a->mainOp == "∀")) {
      return false;
   }
   // regular instance
   foreach ($c->myTerms as $t) {
      if (!(isVar($t))) {
         if (sameWff($c, subTerm($a->rightSide, $t, $a->myLetter))) {
            return true;
         }
      }
   }
   // vacuous binding instance
   if ((!(in_array($a->myLetter,$a->rightSide->allFreeVars))) && (sameWff($c ,$a->rightSide ))) {
      return true;
   }
   return false;
}

function followsByDeMThisWay($a, $b) {
   return (
      ($b->mainOp == "¬")
      &&
      (
         (($a->mainOp == "∧") && ($b->rightSide->mainOp == "∨"))
         ||
         (($a->mainOp == "∨") && ($b->rightSide->mainOp == "∧"))
      )
      &&
      (($a->rightSide->mainOp == "¬") && ($a->leftSide->mainOp == "¬"))
      &&
      (sameWff($a->rightSide->rightSide, $b->rightSide->rightSide))
      &&
      (sameWff($a->leftSide->rightSide, $b->rightSide->leftSide))
   );
}

function followsByDeM($c, $a) {
   return (
      (followsByDeMThisWay($c, $a))
      ||
      (followsByDeMThisWay($a, $c))
   );
}

function followsByDNE($c, $a) {
   return (
      ($a->mainOp == "¬")
      &&
      ($a->rightSide->mainOp == "¬")
      &&
      (sameWff($c, $a->rightSide->rightSide))
   );
}

function followsByMTThisWay($c, $a, $b) {
   return (
      ($a->mainOp == "→")
      &&
      ($b->mainOp == "¬")
      &&
      ($c->mainOp == "¬")
      &&
      (sameWff($a->rightSide, $b->rightSide))
      &&
      (sameWff($a->leftSide, $c->rightSide))
   );
}

function followsByMT($c,$a,$b) {
   return (
      (followsByMTThisWay($c,$a,$b))
      ||
      (followsByMTThisWay($c,$b,$a))
   );
}

function followsByDSThisWay($c,$a,$b) {
   return (
      ($a->mainOp == "∨")
      and
      ($b->mainOp == "¬")
      and
      (
         (
            (sameWff($b->rightSide, $a->rightSide))
            &&
            (sameWff($c,$a->leftSide))
         )
         ||
         (
            (sameWff($b->rightSide, $a->leftSide))
            &&
            (sameWff($c,$a->rightSide))
         )
      )
   );
}

function followsByDS($c,$a,$b) {
   return (
      (followsByDSThisWay($c,$a,$b))
      ||
      (followsByDSThisWay($c,$b,$a))
   );
}

function followsByConjIntroThisWay($rw,$a,$b) {
   return (
      ($rw->mainOp == "∧")
      &&
      (sameWff($rw->rightSide, $a))
      &&
      (sameWff($rw->leftSide, $b))
   );
}

function followsByConjIntro($rw,$a,$b) {
   return (
      followsByConjIntroThisWay($rw,$a,$b) ||
      followsByConjIntroThisWay($rw,$b,$a)
   );
}

function followsByConjElim($rw, $a) {
   return (
      ($a->mainOp == "∧")
      &&
      (
         (sameWff($a->rightSide, $rw))
         ||
         (sameWff($a->leftSide, $rw))
      )
   );
}

function followsByContraIntro($c, $a, $b) {
   return (
      ($c->wffType == "splat")
      &&
      (
         (($b->mainOp == "¬") && (sameWff($a, $b->rightSide)))
         ||
         (($a->mainOp == "¬") && (sameWff($b, $a->rightSide)))
      )
   );
}

function followsByMPThisWay($c, $a, $b) {
   return (
      ($a->mainOp == "→")
      &&
      (sameWff($a->rightSide, $c))
      &&
      (sameWff($a->leftSide, $b))
   );
}

function followsByMP($c, $a, $b) {
   return (
      (followsByMPThisWay($c, $a, $b))
      ||
      (followsByMPThisWay($c, $b, $a))
   );
}

function followsByCP($c, $a, $b) {
   return (
      ($c->mainOp == "→")
      &&
      (sameWff($c->leftSide, $a))
      &&
      (sameWff($c->rightSide, $b))
   );
}

function followsByRAA($c, $a, $b) {
   return (
      ($c->mainOp == "¬")
      &&
      (sameWff($c->rightSide, $a))
      &&
      ($b->wffType == "splat")
   );
}

function followsByIP($c, $a, $b) {
   return (
      ($a->mainOp == "¬")
      &&
      (sameWff($a->rightSide, $c))
      &&
      ($b->wffType == "splat")
   );
}

function followsByTNDThisWay($c, $i, $j, $k, $l) {
   return (
      ($k->mainOp == "¬")
      &&
      (sameWff($k->rightSide, $i))
      &&
      (sameWff($j, $l))
      &&
      (sameWff($c, $j))
   );
}

function followsByTND($c, $i, $j, $k, $l) {
   return (
      (followsByTNDThisWay($c, $i, $j, $k, $l))
      ||
      (followsByTNDThisWay($c, $k, $l, $i, $j))
   );
}

function followsByAdd($c, $a) {
   return (
      ($c->mainOp == "∨")
      &&
      (
         (sameWff($c->leftSide, $a))
         ||
         (sameWff($c->rightSide, $a))
      )
   );
}

function followsByDisjElimThisWay($c, $m, $i, $j, $k, $l) {
   return (
      ($m->mainOp == "∨")
      &&
      (sameWff($m->leftSide, $i))
      &&
      (sameWff($m->rightSide, $k))
      &&
      (sameWff($j, $l))
      &&
      (sameWff($j,$c))
   );
}

function followsByDisjElim($c, $m, $i, $j, $k, $l) {
   return (
      (followsByDisjElimThisWay($c, $m, $i, $j, $k, $l))
      ||
      (followsByDisjElimThisWay($c, $m, $k, $l, $i, $j))
   );
}

function followsByBiconIntroThisWay($c, $i, $j, $k, $l) {
   return (
      ($c->mainOp == "↔")
      &&
      (sameWff($c->leftSide, $i))
      &&
      (sameWff($c->rightSide, $j))
      &&
      (sameWff($c->rightSide, $k))
      &&
      (sameWff($c->leftSide, $l))
   );
}

function followsByBiconIntro($c, $i, $j, $k, $l) {
   return (
      (followsByBiconIntroThisWay($c, $i, $j, $k, $l))
      ||
      (followsByBiconIntroThisWay($c, $k, $l, $i, $j))
   );
}

function followsByBiconElimThisWay($c, $a, $b) {
   return (
      ($a->mainOp == "↔")
      &&
      ((
         (sameWff($a->leftSide, $b))
         &&
         (sameWff($a->rightSide, $c))
      )
       ||
       (
         (sameWff($a->leftSide, $c))
         &&
         (sameWff($a->rightSide, $b))          
       ))
   );
}

function followsByBiconElim($c, $a, $b) {
   return (
      (followsByBiconElimThisWay($c, $a, $b))
      ||
      (followsByBiconElimThisWay($c, $b, $a))
   );
}

function newJ() {
   $j = new StdClass();
   $j->rules = array();
   $j->lines = array();
   $j->subps = array();
   $j->parsedOK = true;
   $j->errMsg = '';
   return $j;
}

function parseJ($jstr) {
   global $predicateSettings, $tfl_rules, $fol_rules;
   $j = newJ();

   $jstr = mb_ereg_replace('[;,\s]+',',',$jstr);
   $jstr = mb_ereg_replace('[-–]+','-',$jstr);
   
   $jparts = explode(',',$jstr);
   foreach ($jparts as $jpart) {
      if ($jpart == '') {
         $j->parsedOK = false;
         $j->errMsg = 'Justification left blank.';
         return $j;
      }
      if (mb_ereg_match('[0-9]*$', $jpart)) {
         array_push($j->lines, intval($jpart) );
         continue;
      }
      if (mb_ereg_match('[0-9]+-[0-9]+$', $jpart)) {
         $spc = new StdClass();
         $jpbreak = explode('-', $jpart);
         $spc->spstart = intval($jpbreak[0]);
         $spc->spend = intval($jpbreak[1]);
         array_push($j->subps, $spc);
         continue;
      }
      if ((in_array($jpart, $tfl_rules)) ||
          ( ($predicateSettings) && (in_array($jpart, $fol_rules )))) {
         array_push($j->rules, $jpart);
      } else {
         $j->parsedOK = false;
         $j->errMsg = 'Justification cites nonexistent rule (' . $jpart . ') or is badly formed.';
         return $j;
      }
   }
   if (count($j->rules) > 1) {
      $j->parsedOK = false;
      $j->errMsg = 'More than one rule cited.';
   }
   if (count($j->rules) < 1) {
      $j->parsedOK = false;
      $j->errMsg = 'No rule cited.';
   }

   return $j;
}

function flatten_proof($pr, $dpth_ar) {
   $fpr = array();
   for ($i=0; $i<count($pr); $i++) {
      if (is_array($pr[$i])) {
         $fpr = array_merge($fpr, flatten_proof($pr[$i], array_merge($dpth_ar, array($i))));
      } else {
         $x = clone $pr[$i];
         $x->location = array_merge($dpth_ar, array($i) );
         $x->issues = array();
         array_push($fpr, $x);
      }
   }
   return $fpr;
}


function check_proof($pr, $numprems, $conc) {
   global $cite_nums;
   $rv = new StdClass();
   $rv->issues = array();
   $rv->concReached = false;
   
   $fpr = flatten_proof($pr, array() );
   
   // check syntax for all
   foreach ($fpr as &$line) {
      $line->wff = parseIt($line->wffstr);
      if (!($line->wff->isWellFormed)) {
         array_push($line->issues, 'Not well-formed: ' . $line->wff->ErrMsg);
      }
   }
   unset($line);
   
   // parse jStr for all
   foreach ($fpr as &$line) {
      $line->j = parseJ($line->jstr);
      if (!($line->j->parsedOK)) {
         array_push($line->issues, 'Cannot parse justification: ' . $line->j->errMsg);
      } 
   }
   unset($line);
   
   // ensure citation cites the right amount of stuff
   foreach ($fpr as &$line) {
      if ($line->j->parsedOK) {
         $cnums = $cite_nums[$line->j->rules[0]];
         $good_lc=$cnums[0];
         $good_spc=$cnums[1];
         $act_lc = count($line->j->lines);
         $act_spc = count($line->j->subps);
         if ($act_lc < $good_lc) {
            array_push($line->issues, 'Cites too few line numbers for the rule ' . $line->j->rules[0] . '.');
         }
         if ($act_lc > $good_lc) {
            array_push($line->issues, 'Cites too many line numbers for the rule ' . $line->j->rules[0] . '.');
         }
         if ($act_spc < $good_spc) {
            array_push($line->issues, 'Cites too few ranges of lines for the rule ' . $line->j->rules[0] . '.');
         }
         if ($act_spc > $good_spc) {
            array_push($line->issues, 'Cites too many ranges of lines for the rule ' . $line->j->rules[0] . '.');
         }
      }
   }
   unset($line);
   
   // ensure cited lines are available
   for ($i=0; $i<count($fpr); $i++) {
      if ($fpr[$i]->j->parsedOK) {
         $n = ($i + 1);
         $nloc = $fpr[$i]->location;
         // individual line citations
         foreach ($fpr[$i]->j->lines as $citedline) {
            if (($citedline > count($fpr)) || ($citedline < 1)) {
               array_push($fpr[$i]->issues, 'Cites nonexistent line (' . $citedline . ').');
               continue;
            }
            if ($citedline == $n) {
               array_push($fpr[$i]->issues, 'Cites itself.');
               continue;
            }
            if ($citedline > $n) {
               array_push($fpr[$i]->issues, 'Cites a line (' . $citedline . ') that occurs after it.');
               continue;
            }
            $cloc = $fpr[($citedline - 1)]->location;
            if (count($cloc) > count($nloc)) {
               array_push($fpr[$i]->issues, 'Cites an unavailable line (' . $citedline . ').');
               continue;
            }
            $problem = false;
            for ($d=0; $d<(count($cloc) - 1); $d++) {
               if ($cloc[$d] != $nloc[$d]) {
                  $problem = true;
                  break;
               }
            }
            if ($problem) {
               array_push($fpr[$i]->issues, 'Cites an unavailable line (' . $citedline . ').');
               continue;  
            }
         }
         // line range citations
         foreach ($fpr[$i]->j->subps as $citedsp) {
            $startcite = $citedsp->spstart;
            $endcite = $citedsp->spend;
            if ($startcite > $endcite) {
               array_push($fpr[$i]->issues, 'Cites a range of lines in the wrong order (' . $startcite . '–' . $endcite . ').');
               continue;
            }
            if (($startcite > count($fpr)) || ($endcite > count($fpr)) || ($startcite < 1) || ($endcite < 0)) {
               array_push($fpr[$i]->issues, 'Cites a line nonexistent range of lines (' . $startcite . '–' . $endcite . ').');
               continue;
            }
            if ($endcite >= $n) {
               array_push($fpr[$i]->issues, 'Cites a line range after or including itself (' . $startcite . '–' . $endcite . ').');
               continue;
            }
            // ensure an actual subproof
            $endloc = $fpr[($endcite - 1)]->location;
            $startloc = $fpr[($startcite - 1)]->location;
            $problem = false;
            if (count($endloc) != count($startloc)) {
               $problem = true;
            }
            if ($startloc[count($startloc) - 1] != 0) {
               $problem = true;
            }
            for ($l=0; $l<(count($startloc) - 1); $l++) {
               if ($endloc[$l] != $startloc[$l]) {
                  $problem = true;
                  break;
               }
            }
            if ($problem) {
               array_push($fpr[$i]->issues, 'Cites a range of lines which do not make up a subproof (' . $startcite . '–' . $endcite . ').');
               continue;
            }
            // ensure subproof is available
            $problem = false;
            $cloc = $startloc;
            array_pop($cloc);
            if ((count($cloc) > count($nloc)) || (count($cloc) < count($nloc))) {
               array_push($fpr[$i]->issues, 'Cites an unavailable subproof (' . $startcite . '–' . $endcite . ').');
               continue;
            }
            for ($d=0; $d<(count($cloc) - 1); $d++) {
               if ($cloc[$d] != $nloc[$d]) {
                  $problem = true;
                  break;
               }
            }
            if ($problem) {
               array_push($fpr[$i]->issues, 'Cites an unavailable subproof (' . $startcite . '–' . $endcite . ').');
               continue;  
            }           
         }
      }
   }
   
   // make sure cited lines are well-formed
   for ($i=0; $i<count($fpr); $i++) {
      $fpr[$i]->canBeChecked = true;
      if ( count($fpr[$i]->issues) > 0 ) {
         $fpr[$i]->canBeChecked = false;
         continue;
      }
      foreach ($fpr[$i]->j->lines as $cl) {
         $cn = $cl - 1;
         if (!($fpr[$cn]->wff->isWellFormed)) {
            $fpr[$i]->canBeChecked = false;
            array_push($fpr[$i]->issues, 'Cites another line that is not well-formed (' . $cl . ').'); 
         }
      }
      foreach ($fpr[$i]->j->subps as $csp) {
         $csn = $csp->spstart - 1;
         $cen = $csp->spend - 1;
         if (!($fpr[$csn]->wff->isWellFormed)) {
            $fpr[$i]->canBeChecked = false;
            array_push($fpr[$i]->issues, 'Cites another line that is not well-formed (' . $csp->spstart . ').'); 
         }
         if (!($fpr[$cen]->wff->isWellFormed)) {
            $fpr[$i]->canBeChecked = false;
            array_push($fpr[$i]->issues, 'Cites another line that is not well-formed (' . $csp->spend . ').'); 
         }
      }
   }

   // check lines that can be checked
   //////////////////////////////////
   // ENFORCING RULES GOES HERE
   //////////////////////////////////
   for ($i=0; $i<count($fpr); $i++) {
      // skip lines with other problems
      if (!($fpr[$i]->canBeChecked)) {
         continue;
      }
      $worked = false;
      switch ($fpr[$i]->j->rules[0]) {
         case "Pr":
            $worked = (($i + 1) <= $numprems);
            break;
         case "Hyp":
            $worked = ($fpr[$i]->location[ (count($fpr[$i]->location) - 1) ] == 0); 
            break;
         case "∧I":
            $worked = followsByConjIntro($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "∧E":
            $worked = followsByConjElim($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "⊥E":
            $worked = ( $fpr[ ($fpr[$i]->j->lines[0] - 1) ]->wff->wffType == "splat");
            break;
         case "⊥I":
            $worked = followsByContraIntro($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "→E":
            $worked = followsByMP( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "→I":
            $worked = followsByCP( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff);
            break;
         case "¬I":
            $worked = followsByRAA( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff);
            break;
         case "¬E":
            $worked = followsByContraIntro($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "IP":
            $worked = followsByIP( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff);
            break;
	 case "TND":
            $worked = followsByTND( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spend - 1  )]->wff);            
	 case "LEM":
            $worked = followsByTND( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spend - 1  )]->wff);            
            break;
         case "∨I":
            $worked = followsByAdd($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "∨E":
            $worked = followsByDisjElim( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spend - 1  )]->wff);               
            break;
         case "↔I":
            $worked = followsByBiconIntro( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spstart - 1  )]->wff, $fpr[( $fpr[$i]->j->subps[1]->spend - 1  )]->wff); 
            break;
         case "↔E":
            $worked = followsByBiconElim( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "X":
            $worked = ( $fpr[ ($fpr[$i]->j->lines[0] - 1) ]->wff->wffType == "splat");
            break;
	 case "DS":
            $worked = followsByDS( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff );
            break;
         case "R":
            $worked = sameWff($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff );
            break;
         case "MT":
            $worked = followsByMT($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff);
            break;
         case "DNE":
            $worked = followsByDNE($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "DeM":
            $worked = followsByDeM($fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "∀E":
            $worked = followsByUI( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "∃I":
            $worked = followsByEG( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
         case "∀I":
            $univ = $fpr[$i]->wff;
            if ($univ->mainOp == "∀") {
               $inst = $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff;
               $bound_var = $univ->myLetter;
               if (in_array($univ->myLetter, $univ->rightSide->allFreeVars)) {
                  $worked = false;
                  foreach ($inst->myTerms as $t) {
                     if (in_array($t, $univ->myTerms)) {
                        continue;
                     }
                     if (!(isVar($t))) {
                        if (sameWff($inst, subTerm($univ->rightSide, $t, $bound_var))) {
                           $found = false;
                           for ($j=0; $j<$i; $j++) {
                              if (($fpr[$j]->j->rules[0] == "Pr") || ($fpr[$j]->j->rules[0] == "Hyp")) {
                                 $hyp_loc = $fpr[$j]->location;
                                 $this_loc = $fpr[$i]->location;


                                 if (count($hyp_loc) > count($this_loc)) {
                                    continue;
                                 }
                                 $problem = false;
                                 for ($d=0; $d<(count($hyp_loc) - 1); $d++) {
                                    if ($hyp_loc[$d] != $this_loc[$d]) {
                                       $problem = true;
                                       break;
                                    }
                                 }
                                 if (!($problem)) {
                                    if ( in_array($t, $fpr[$j]->wff->myTerms)) {
                                       $found = true;
                                       break;
                                    }
                                 }



                              }
                           }
                           if ($found) {
                              continue;
                           }
                           $worked = true;
                        } 
                     }
                  }
               } else {
                  $worked = sameWff($univ->rightSide, $inst);
               }
            } else {
               $worked = false;
            }
            break;
         case "∃E":
            $exwff = $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff;
            if ($exwff->mainOp == "∃") {
               $sp_hyp = $fpr[( $fpr[$i]->j->subps[0]->spstart - 1  )]->wff;
               $sp_res = $fpr[( $fpr[$i]->j->subps[0]->spend - 1  )]->wff;
               $res = $fpr[$i]->wff;
               if (sameWff($sp_res, $res)) {
                  if (in_array( $exwff->myLetter, $exwff->rightSide->allFreeVars )) {
                     $worked = false;
                     foreach ($sp_hyp->myTerms as $t) {
                        if (!(isVar($t))) {
                           if (sameWff($sp_hyp, subTerm($exwff->rightSide, $t, $exwff->myLetter ))) {
                              if (in_array($t, $res->myTerms)) {
                                 continue;
                              }
                              if (in_array($t, $exwff->myTerms)) {
                                 continue;
                              }
                              
                              $found = false;
                              for ($j=0; $j<$i; $j++) {
                                 if (($fpr[$j]->j->rules[0] == "Pr") || ($fpr[$j]->j->rules[0] == "Hyp")) {
                                    $hyp_loc = $fpr[$j]->location;
                                    $this_loc = $fpr[$i]->location;


                                    if (count($hyp_loc) > count($this_loc)) {
                                       continue;
                                    }
                                    $problem = false;
                                    for ($d=0; $d<(count($hyp_loc) - 1); $d++) {
                                       if ($hyp_loc[$d] != $this_loc[$d]) {
                                          $problem = true;
                                          break;
                                       }
                                    }
                                    if (!($problem)) {
                                       if ( in_array($t, $fpr[$j]->wff->myTerms)) {
                                          $found = true;
                                          break;
                                       }
                                    }



                                 }
                              }
                              if ($found) {
                                 continue;
                              }
                              $worked = true;
                              
                              
                           }
                        }
                     }
                  } else {
                     $worked = sameWff($exwff->rightSide, $sp_hyp);
                  }
               } else {
                  $worked = false;
               }
            } else {
               $worked = false;
            }
            
            break;
         case "=I":
            $worked = isSelfId( $fpr[$i]->wff );
            break;
         case "=E":
            $worked = followsByLL( $fpr[$i]->wff, $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff, $fpr[( $fpr[$i]->j->lines[1] - 1  )]->wff );
            break;
         case "CQ":
            $worked = followsByCQ($fpr[$i]->wff , $fpr[( $fpr[$i]->j->lines[0] - 1  )]->wff);
            break;
      }
      if (!($worked)) {
         array_push($fpr[$i]->issues, 'Is not a proper application of the rule ' . $fpr[$i]->j->rules[0] .' (for the line(s) cited).'); 
      }
   }
   
   
   // merge issues
   for ($i = 0; $i<count($fpr) ; $i++) {
      $n = ($i + 1);
      $l = $fpr[$i];
      foreach ($l->issues as $issue) {
         array_push($rv->issues, 'Line ' . $n . ': ' . $issue);
      }
   }
   

   // if no issues look for conclusion
   if (count($rv->issues) == 0) {
      $conc_wff = parseIt($conc);
      if (!($conc_wff->isWellFormed)) {
         array_push($rv->issues, 'Desired conclusion is not a wff. Oops!');
      } else {
         foreach ($fpr as $line) {
            if ((count($line->location) == 1) && (sameWff($line->wff, $conc_wff))) {
               $rv->concReached = true;
            } 
         }
         unset($line);
      }
   }
      
   
   return $rv;
}

?>