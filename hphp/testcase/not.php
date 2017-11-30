<?php

$multi = NULL;
add_multi($multi, true, 1);
add_multi($multi, false, 2);

$not = !$multi;

echo $not;
echo "\n";
