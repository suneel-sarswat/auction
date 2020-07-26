#!/bin/bash


printf "%s\n" "Running list results"

coqc GenReflect.v

coqc SetSpecs.v

coqc DecSort.v

coqc MinMax.v

coqc DecType.v

coqc SetReflect.v

coqc DecList.v

coqc MoreDecList.v

printf "%s\n" "Running essential definitions and results"
coqc BidAsk.v

coqc Matching.v

coqc AuctionInvar.v

coqc IndRat.v

printf "%s\n" "Runing fair matching results"
coqc Fair.v

printf "%s\n" "Running maximum matching results"
coqc MM.v

printf "%s\n" "Running uniform matching results"
coqc UM.v

printf "%s\n" "Ruuning results on bounds"
coqc Bounds.v


printf "%s\n" "Done"
coqc Bounds.v



