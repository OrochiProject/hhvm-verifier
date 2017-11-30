<?php

$multi_arr = NULL;
$multi_arr = add_multi($multi_arr, ["W" => "917", "C" => "646"], 1);
$multi_arr = add_multi($multi_arr, ["E" => "917", "C" => "124"], 2);

$arr = array("C" => "646", "W" => "917");

$multi_key = NULL;
$multi_key = add_multi($multi_key, "C", 1);
$multi_key = add_multi($multi_key, "W", 2);

$key = "W";

print("AKExists (array_key_exists(key, array):\n");

$result = array_key_exists($key, $arr);
print("(S, S):  ");
print($result);
print("\n");

$result = array_key_exists($multi_key, $arr);
print("(M, S):  ");
print($result);
print("\n");

$result = array_key_exists($key, $multi_arr);
print("(S, M):  ");
print($result);
print("\n");

$result = array_key_exists($multi_key, $multi_arr);
print("(M, M):  ");
print($result);
print("\n");
