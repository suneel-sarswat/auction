Formal Verification of Financial Algorithms.

This work aims to formally verify different algorithms used in finance. Matching algorithms used by exchanges are at the core of broad spectrum of financial algorithms. This folder contains the formalisation of matching algorithm used by exchanges to match demand and supply for trading. The project is split into the following files:

1. GenReflect.v: Contains common results on reflection techniques.

2. SetSpecs.v: Common predicates over sets.

3. DecSort.v: Sorting a list using a decidable binary relation.

4. MinMax.v: Min and Max in a list.

5. DecType.v: Type with decidable equality.

6. SetReflect.v: Reflection lemmas for sets on decidable types

7. DecList.v: Lists on decidable types

8. MoreDecList.v: More results on Lists on decidable types (not needed for sets)

9. BidAsk.v: This file contains basic definitions of Bids, Asks and Fill (type of trade output). We also define projection functions on list of Bids and Asks. 

10. Matching.v: This file contains useful definitions and basic properties of fundamental concepts about trading such as matching, maximum matching (MM), individual rational matching (IR), uniform matching, fair matching etc. This file also contains important results on matchings, IR matchings, uniform matchings.

11. IndRat.v: Main results of Individual Rational (IR) matchings.

12. Fair.v: This file contains all the results about fair matching and a function to compute fair matching from any given matching. The main result is existence of a fair matching without compromise of it's size.

13. MM.v: This file contains results of maximum matchings and a function produce_MM to compute maximum matching from a given list of bids and list of asks. The main result is proof that the matching produced by the function produce_MM is maximum.

14. UM.v: This file contains results of uniform matchings and a function produce_UM to compute uniform matching from a given list of bids and list of asks. The main result is proof that the matching produced by the function produce_UM is maximum among all the uniform matching.

The file auction.sh can be used to compile all the above the files.
