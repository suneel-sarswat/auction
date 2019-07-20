Formal Verification of Financial Algorithms.

This work aims to formally verify different algorithms used in finance. Matching algorithms used by exchanges are at the core of broad spectrum of financial algorithms. This folder contains the formalisation of matching algorithm used by exchanges to match demand and supply for trading. The project is split into the following files:

GenReflect.v: Contains common results on reflection techniques.

SetSpecs.v: Common predicates over sets.

Sorting.v: Sorting a list using a decidable binary relation.

MinMax.v: Min and Max in a list.

DecType.v: Type with decidable equality.

SetReflect.v: Reflection lemmas for sets on decidable types

DecList.v: Lists on decidable types

MoreDecList.v: More results on Lists on decidable types (not needed for sets)

BidAsk.v: This file contains basic definitions of Bids, Asks and Fill (type of trade output). We also define projection functions on list of Bids and Asks. 

Matching.v: This file contains useful definitions and basic properties of fundamental concepts about trading such as matching, maximum matching (MM), individual rational matching (IR), uniform matching, fair matching etc. This file also contains important results on matchings, IR matchings, uniform matchings.

IndRat.v: Main results of Individual Rational (IR) matchings.

Fair.v: This file contains all the results about fair matching and a function to compute fair matching from any given matching. The main result is existence of a fair matching without compromise of it's size.

MM.v: This file contains results of maximum matchings and a function produce_MM to compute maximum matching from a given list of bids and list of asks. The main result is proof that the matching produced by the function produce_MM is maximum.

UM.v: This file contains results of uniform matchings and a function produce_UM to compute uniform matching from a given list of bids and list of asks. The main result is proof that the matching produced by the function produce_UM is maximum among all the uniform matching.

The file auction.sh can be used to compile all the above the files.