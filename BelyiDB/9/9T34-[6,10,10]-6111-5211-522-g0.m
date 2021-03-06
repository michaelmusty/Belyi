s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,10,10]-6111-5211-522-g0";
s`BelyiDBFilename := "9T34-[6,10,10]-6111-5211-522-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 10, 10 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 12;
s`BelyiDBPointedSize := 12;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 7, 2, 5, 4, 3, 8, 6, 9, 1 ],
[ 7, 9, 2, 5, 4, 3, 1, 6, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 9, 7, 4, 3, 6, 8, 1, 2 ],
[ 6, 8, 9, 5, 4, 1, 3, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 3, 6, 8, 7, 5, 4, 1 ],
[ 4, 9, 2, 3, 8, 7, 6, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 8, 7, 4, 5, 9, 2, 1, 6 ],
[ 9, 8, 7, 1, 4, 5, 3, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 5, 7, 8, 6, 3, 4, 1 ],
[ 6, 9, 2, 7, 8, 3, 4, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 8, 7, 4, 3, 6, 2, 5, 1 ],
[ 6, 9, 7, 5, 4, 8, 3, 2, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 7, 4, 3, 8, 6, 5, 1 ],
[ 7, 9, 2, 5, 4, 8, 3, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 2, 7, 6, 5, 4, 8, 9, 1 ],
[ 4, 9, 2, 1, 6, 5, 3, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 4, 3, 2, 7, 6, 8, 9, 1 ],
[ 6, 9, 4, 3, 2, 1, 5, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 8, 7, 5, 4, 3, 6, 1 ],
[ 8, 9, 2, 7, 6, 5, 4, 3, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
\[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 8, 3, 9, 7, 6, 2, 1, 4 ],
[ 6, 8, 7, 3, 9, 1, 5, 2, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 4, 3, 2, 5, 7, 8, 1, 6 ],
[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 7, 2, 5, 4, 3, 8, 6, 9, 1 ],
[ 7, 9, 2, 5, 4, 3, 1, 6, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 9, 7, 4, 3, 6, 8, 1, 2 ],
[ 6, 8, 9, 5, 4, 1, 3, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 3, 6, 8, 7, 5, 4, 1 ],
[ 4, 9, 2, 3, 8, 7, 6, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 8, 7, 4, 5, 9, 2, 1, 6 ],
[ 9, 8, 7, 1, 4, 5, 3, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 5, 7, 8, 6, 3, 4, 1 ],
[ 6, 9, 2, 7, 8, 3, 4, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 8, 7, 4, 3, 6, 2, 5, 1 ],
[ 6, 9, 7, 5, 4, 8, 3, 2, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 7, 4, 3, 8, 6, 5, 1 ],
[ 7, 9, 2, 5, 4, 8, 3, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 2, 7, 6, 5, 4, 8, 9, 1 ],
[ 4, 9, 2, 1, 6, 5, 3, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 4, 3, 2, 7, 6, 8, 9, 1 ],
[ 6, 9, 4, 3, 2, 1, 5, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 8, 7, 5, 4, 3, 6, 1 ],
[ 8, 9, 2, 7, 6, 5, 4, 3, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 8, 3, 9, 7, 6, 2, 1, 4 ],
[ 6, 8, 7, 3, 9, 1, 5, 2, 4 ]
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
