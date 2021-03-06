s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[14,3,4]-72-33111-4221-g0";
s`BelyiDBFilename := "9T34-[14,3,4]-72-33111-4221-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 14, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 10;
s`BelyiDBPointedSize := 10;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 2, 8, 7, 4, 5, 6, 9, 1, 3 ],
[ 1, 9, 4, 5, 6, 3, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 1, 7, 4, 6, 5, 3, 8, 2, 9 ],
[ 8, 6, 3, 5, 4, 2, 1, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 9, 4, 3, 5, 2, 1, 7, 8, 6 ],
[ 5, 3, 2, 4, 9, 7, 6, 1, 8 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 3, 2, 5, 4, 1, 7, 9, 8, 6 ],
[ 2, 1, 4, 3, 9, 6, 5, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 8, 2, 3, 5, 9, 1, 7, 6, 4 ],
[ 2, 3, 9, 4, 8, 7, 6, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 5, 4, 3, 8, 6, 1, 7, 2, 9 ],
[ 8, 3, 2, 1, 5, 7, 6, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 6, 4, 3, 5, 2, 8, 7, 1, 9 ],
[ 5, 3, 2, 4, 1, 7, 8, 9, 6 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 8, 2, 5, 4, 7, 6, 3, 9, 1 ],
[ 2, 7, 4, 3, 6, 5, 9, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 1, 5, 3, 8, 7, 6, 2, 9, 4 ],
[ 7, 3, 9, 2, 6, 5, 1, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
\[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 9, 8 ],
[ 9, 2, 3, 6, 5, 8, 1, 4, 7 ],
[ 2, 3, 8, 5, 4, 9, 7, 1, 6 ]
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
[ 4, 5, 2, 3, 9, 7, 6, 1, 8 ],
[ 1, 8, 3, 4, 7, 2, 9, 6, 5 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 3, 2, 7, 6, 8, 9, 1, 5 ],
[ 1, 8, 3, 2, 5, 9, 6, 4, 7 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 4, 9, 5, 8, 7, 2, 1, 3 ],
[ 3, 8, 7, 4, 2, 6, 1, 5, 9 ],
[ 2, 3, 9, 5, 4, 7, 6, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 5, 4, 3, 6, 7, 8, 1, 2 ],
[ 3, 8, 9, 4, 5, 2, 7, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 6, 9, 7, 3, 4, 5 ],
[ 5, 2, 3, 9, 8, 6, 4, 1, 7 ],
[ 2, 3, 9, 5, 4, 7, 6, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 7, 4, 2, 6, 1, 5, 9, 8 ],
[ 8, 6, 3, 1, 5, 7, 2, 4, 9 ],
[ 2, 8, 4, 3, 6, 5, 7, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 3, 2, 7, 6, 9, 5, 1, 8 ],
[ 1, 8, 3, 2, 5, 7, 9, 4, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 5, 2, 9, 6, 7, 8, 1, 4 ],
[ 9, 8, 3, 1, 5, 2, 7, 6, 4 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 1, 5, 9, 6, 7, 8, 2, 4 ],
[ 9, 2, 8, 1, 5, 3, 7, 6, 4 ],
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 2, 5, 6, 8, 9, 3, 7 ],
[ 7, 2, 3, 4, 1, 9, 5, 6, 8 ],
[ 2, 3, 9, 5, 4, 7, 6, 8, 1 ]
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
