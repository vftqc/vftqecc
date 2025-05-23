#!/bin/bash

echo "Table 1" > Table1_results.txt
echo " " >> Table1_results.txt

param_list=(
  "ColorCode prep 3"
  "ColorCode cnot 3"
  "ColorCode meas 3"
  "ColorCode ec 3"
  "ColorCode prep 5"
  "ColorCode cnot 5"
  "ColorCode meas 5"
  "ColorCode ec 5"
  "RotatedSurfaceCode prep 3"
  "RotatedSurfaceCode cnot 3"
  "RotatedSurfaceCode meas 3"
  "RotatedSurfaceCode ec 3"
  "RotatedSurfaceCode prep 5"
  "RotatedSurfaceCode cnot 5"
  "RotatedSurfaceCode meas 5"
  "RotatedSurfaceCode ec 5"
  "ToricCode prep 3"
  "ToricCode cnot 3"
  "ToricCode meas 3"
  "ToricCode ec 3"
  "ToricCode prep 5"
  "ToricCode cnot 5"
  "ToricCode meas 5"
  "ToricCode ec 5"
  "QuantumReedMullerCode ec 3"
  "RotatedSurfaceCode prep 7"
  "RotatedSurfaceCode meas 7 13"
  "RotatedSurfaceCode ec 7"
)

for params in "${param_list[@]}"; do
  read -a args <<< "$params"

  echo "Running: ${args[*]}"
  output=$(julia example/${args[0]}.jl "${args[@]:1}")
  last_two_lines=$(echo "$output" | tail -n 2)

  echo "${args[*]}" >> Table1_results.txt
  echo "$last_two_lines" >> Table1_results.txt
  echo " " >> Table1_results.txt
done
