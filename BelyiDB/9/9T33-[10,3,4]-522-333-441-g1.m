s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[10,3,4]-522-333-441-g1";
s`BelyiDBFilename := "9T33-[10,3,4]-522-333-441-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 10, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 7, 6, 9, 8 ],
[ 8, 1, 7, 9, 4, 3, 6, 2, 5 ],
[ 8, 6, 5, 9, 2, 3, 7, 4, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 7, 6, 9, 8 ],
[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
[ 9, 4, 5, 3, 2, 6, 8, 1, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 7, 6, 9, 8 ],
[ 3, 6, 4, 1, 7, 9, 8, 5, 2 ],
[ 9, 1, 3, 8, 4, 5, 2, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
\[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 7, 6, 9, 8 ],
[ 9, 4, 5, 7, 6, 3, 2, 1, 8 ],
[ 7, 6, 2, 3, 8, 4, 5, 1, 9 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 4, 8, 7, 1, 9, 5, 3, 6 ],
[ 8, 5, 2, 1, 3, 7, 9, 4, 6 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 5, 6, 1, 2, 3, 8, 4, 7 ],
[ 8, 4, 5, 6, 7, 2, 3, 9, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 5, 4, 8, 2, 3, 1, 9, 6, 7 ],
[ 2, 6, 4, 5, 3, 1, 8, 9, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 6, 9, 4, 3, 7, 8, 1, 5, 2 ],
[ 4, 3, 9, 7, 6, 8, 1, 5, 2 ],
[ 4, 3, 1, 2, 6, 7, 8, 5, 9 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
