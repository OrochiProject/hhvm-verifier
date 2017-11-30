<?php

$s1 = "abc";
$s2 = "def";

$multi = NULL;
$multi = add_multi($multi, "ghi", 1);
$multi = add_multi($multi, "jkl", 2);

$multi2 = NULL;
$multi2 = add_multi($multi2, "mno", 1);
$multi2 = add_multi($multi2, "pqr", 2);

$s = $s1 . $s2;
print("(S, S):\n");
print(" > ");
print($s1);
print(" . ");
print($s2);
print(" = ");
print($s);
print("\n");

$s = $multi . $s1;
print("(M, S):\n");
print(" > ");
print($multi);
print(" . ");
print($s1);
print(" = ");
print($s);
print("\n");

$s = $s1 . $multi;
print("(S, M):\n");
print(" > ");
print($s1);
print(" . ");
print($multi);
print(" = ");
print($s);
print("\n");

$s = $multi . $multi2;
print("(M, M):\n");
print(" > ");
print($multi);
print(" . ");
print($multi2);
print(" = ");
print($s);
print("\n");
