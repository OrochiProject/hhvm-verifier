<?php

$multi = NULL;
$multi = add_multi($multi, 1, 0);
$multi = add_multi($multi, 3, 1);
$multi = add_multi($multi, 6, 2);

print("Starting...\n");
print($multi);
print("\n");

print("multi++: ");
$multi++;
print($multi);
print("\n");

print("++multi: ");
++$multi;
print($multi);
print("\n");

print("multi--: ");
$multi--;
print($multi);
print("\n");

print("--multi: ");
--$multi;
print($multi);
print("\n");
