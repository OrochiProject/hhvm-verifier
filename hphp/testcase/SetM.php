<?php

$key = 'G';
$val = 7;

$multi_arr = NULL;
$multi_arr = add_multi($multi_arr, ['C' => 3], 1);
$multi_arr = add_multi($multi_arr, ['D' => 4, 'E' => 5], 2);

$multi_key = NULL;
$multi_key = add_multi($multi_key, 'A', 1);
$multi_key = add_multi($multi_key, 'B', 2);

$multi_val = NULL;
$multi_val = add_multi($multi_val, 1, 1);
$multi_val = add_multi($multi_val, 2, 2);

function print_arr($arr) {
  print("[");
  foreach($arr as $val) {
    print($val);
    print(", ");
  }
  print("]");
}

$arr = [];
print("(S, S, S):\nArr: ");
print_arr($arr);
print(", Key: ");
print($key);
print(", Val: ");
print($val);
print("\nResult: ");
$arr[$key] = $val;
print_arr($arr);
print("\n");

/*
$arr = [];
print("(S, M, S):\nArr: ");
print_arr($arr);
print(", Key: ");
print($multi_key);
print(", Val: ");
print($val);
print("\nResult: ");
$arr[$multi_key] = $val;
print_arr($arr);
print("\n");

$arr = [];
print("(S, S, M):\nArr: ");
print_arr($arr);
print(", Key: ");
print($key);
print(", Val: ");
print($multi_val);
print("\nResult: ");
$arr[$key] = $multi_val;
print_arr($arr);
print("\n");

print("(S, M, M):\nArr: ");
print_arr($arr);
print(", Key: ");
print($multi_key);
print(", Val: ");
print($multi_val);
print("\nResult: ");
$arr[$multi_key] = $multi_val;
print_arr($arr);
print("\n");
 */

print("(M, S, S):\nArr: ");
print($multi_arr);
print(", Key: ");
print($key);
print(", Val: ");
print($val);
print("\nResult: ");
$multi_arr[$key] = $val;
print($multi_arr);
print("\n");
/*
$multi = $multi_arr;
print("(M, M, S):\nArr: ");
print($multi);
print(", Key: ");
print($multi_key);
print(", Val: ");
print($val);
print("\nResult: ");
$multi[$multi_key] = $val;
print($multi);
print("\n");

$multi = $multi_arr;
print("(M, S, M):\nArr: ");
print($multi);
print(", Key: ");
print($key);
print(", Val: ");
print($multi_val);
print("\nResult: ");
$multi[$key] = $multi_val;
print($multi);
print("\n");

$multi = $multi_arr;
print("(M, M, M):\nArr: ");
print($multi);
print(", Key: ");
print($multi_key);
print(", Val: ");
print($multi_val);
print("\nResult: ");
$multi[$multi_key] = $multi_val;
print($multi);
print("\n");
 */
