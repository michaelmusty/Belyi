s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,2,7]-81-222111-711-g0";
s`BelyiDBFilename := "9T34-[8,2,7]-81-222111-711-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 2, 7 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 10;
s`BelyiDBPointedSize := 10;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 4, 3, 5, 6, 7, 9, 8 ],
[ 1, 4, 3, 5, 6, 7, 9, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 4, 3, 5, 6, 9, 8, 7 ],
[ 1, 4, 3, 5, 6, 9, 8, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 4, 3, 5, 9, 7, 8, 6 ],
[ 1, 4, 3, 5, 9, 7, 8, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 4, 3, 9, 6, 7, 8, 5 ],
[ 1, 4, 3, 9, 6, 7, 8, 2, 5 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 3, 5, 4, 6, 7, 9, 8 ],
[ 1, 3, 5, 4, 6, 7, 9, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 9, 5, 4, 6, 7, 8, 3 ],
[ 1, 9, 5, 4, 6, 7, 8, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 3, 5, 4, 6, 9, 8, 7 ],
[ 1, 3, 5, 4, 6, 9, 8, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 3, 5, 4, 9, 7, 8, 6 ],
[ 1, 3, 5, 4, 9, 7, 8, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 3, 4, 6, 5, 7, 9, 8 ],
[ 1, 3, 4, 6, 5, 7, 9, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 9, 4, 6, 5, 7, 8, 3 ],
[ 1, 9, 4, 6, 5, 7, 8, 2, 3 ]
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
[ 8, 3, 1, 2, 4, 5, 6, 7, 9 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
[ 2, 5, 3, 4, 6, 7, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 3, 1, 6, 4, 2, 5, 7, 9 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
[ 2, 6, 3, 4, 7, 5, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 9, 1, 3, 5, 4, 6, 7, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 4, 2, 3, 5, 6, 7, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 8, 9, 3, 5, 4, 6, 7, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 9, 2, 3, 5, 6, 7, 8, 1, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 9, 1, 3, 5, 7, 4, 6, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 4, 2, 3, 7, 6, 8, 5, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 9, 3, 5, 4, 6, 1, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 8, 2, 3, 5, 6, 7, 1, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 8, 9, 3, 5, 7, 4, 6, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 9, 2, 3, 7, 6, 8, 5, 1, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 6, 9, 3, 5, 4, 1, 7, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 7, 2, 3, 5, 6, 1, 8, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 6, 9, 3, 5, 7, 4, 1, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 8, 2, 3, 7, 6, 1, 5, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 3, 8, 2, 4, 5, 6, 1, 9 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ],
[ 8, 5, 3, 4, 6, 7, 9, 2, 1 ]
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
