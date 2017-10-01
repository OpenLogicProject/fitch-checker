<?php

if (!(isset($_POST))) {
   return;
}

if (!(isset($_POST["proofData"]))) {
   return;
}

if (!(isset($_POST["numPrems"]))) {
   return;
}

if (!(isset($_POST["wantedConc"]))) {
   return;
}

$pr_data_json = $_POST["proofData"];

$pr_data = json_decode($_POST["proofData"]);

if (json_last_error() != JSON_ERROR_NONE) {
   return;
}

require 'syntax.php';

$predicateSettings = ($_POST["predicateSettings"] == "true") ?? false;

$wantedConc = $_POST["wantedConc"];

$numprems = intval($_POST["numPrems"]);

require 'proofs.php';

$check_result = check_proof($pr_data, $numprems, $wantedConc);

echo json_encode($check_result);

exit;
?>