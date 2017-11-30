<?php
$key = 'G';
$val = 7;

$multi_key = NULL;
$multi_key = add_multi($multi_key, 'A', 0);
$multi_key = add_multi($multi_key, 'B', 1);

$multi_val = NULL;
$multi_val = add_multi($multi_val, 1, 0);
$multi_val = add_multi($multi_val, 2, 1);

$multi_key2 = NULL;
$multi_key2 = add_multi($multi_key2, 'C', 0);
$multi_key2 = add_multi($multi_key2, 'D', 1);

$multi_val2 = NULL;
$multi_val2 = add_multi($multi_val2, 3, 0);
$multi_val2 = add_multi($multi_val2, 4, 1);

function print_arr($arr) {
  print("[");
  foreach($arr as $val) {
    print($val);
    print(", ");
  }
  print("]");
}

print("Starting...\n");
$arr = array($key => $val);
print("(S, S, S): ");
print_arr($arr);
print("\n");

$arr5 = array($key => $multi_val);
print("(S, S, M): ");
print($arr5);
print("\n");

$arr4 = array($multi_key => $val);
print("(S, M, S): ");
print($arr4);
print("\n");

$arr2 = array($multi_key => $multi_val);
print("(S, M, M): ");
print($arr2);
print("\n");

$arr8 = array($multi_key => $multi_val, $key => $val);
print("(M, S, S): ");
print($arr8);
print("\n");

$arr6 = array($multi_key => $multi_val, $key => $multi_val2);
print("(M, S, M): ");
print($arr6);
print("\n");

$arr7 = array($multi_key => $multi_val, $multi_key2 => $val);
print("(M, M, S): ");
print($arr7);
print("\n");

$arr3 = array($multi_key => $multi_val, $multi_key2 => $multi_val2);
print("(M, M, M): ");
print($arr3);
print("\n");
?>
