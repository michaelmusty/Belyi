s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,4,6]-81-42111-3222-g0";
s`BelyiDBFilename := "9T34-[8,4,6]-81-42111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 12;
s`BelyiDBPointedSize := 12;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 3, 2, 5, 4, 9, 6, 7 ],
[ 2, 1, 4, 3, 6, 5, 8, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 3, 7, 5, 4, 9, 2, 6 ],
[ 2, 1, 8, 3, 6, 5, 9, 4, 7 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 3, 6, 5, 4, 2, 9, 7 ],
[ 2, 1, 7, 3, 6, 5, 4, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 7, 4, 5, 3, 9, 2, 6 ],
[ 2, 1, 8, 6, 4, 5, 9, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 6, 4, 5, 3, 2, 9, 7 ],
[ 2, 1, 7, 6, 4, 5, 3, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 7, 4, 3, 6, 9, 2, 5 ],
[ 2, 1, 8, 5, 4, 9, 6, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 9, 4, 3, 6, 5, 2, 7 ],
[ 2, 1, 8, 5, 4, 7, 6, 9, 3 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 7, 4, 9, 6, 5, 2, 3 ],
[ 2, 1, 8, 9, 4, 7, 6, 3, 5 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 5, 4, 3, 6, 2, 9, 7 ],
[ 2, 1, 7, 5, 4, 3, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 9, 4, 7, 6, 5, 3, 2 ],
[ 2, 1, 9, 8, 4, 7, 6, 5, 3 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 7, 9, 5, 6, 4, 2, 3 ],
[ 2, 1, 8, 9, 7, 5, 6, 3, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 9, 7, 5, 6, 4, 3, 2 ],
[ 2, 1, 9, 8, 7, 5, 6, 4, 3 ]
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
[ 5, 9, 3, 2, 8, 4, 6, 7, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 3, 2, 5, 4, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 3, 2, 7, 4, 6, 1, 8 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 3, 2, 5, 4, 7, 6, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 8, 4, 7, 2, 5, 6, 1, 9 ],
[ 2, 3, 9, 5, 4, 6, 7, 8, 1 ],
[ 8, 4, 9, 2, 6, 7, 5, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 8, 4, 6, 2, 5, 1, 7, 9 ],
[ 2, 3, 9, 5, 4, 6, 7, 8, 1 ],
[ 7, 4, 9, 2, 6, 5, 8, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 2, 9, 5, 8, 3, 4, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 1, 5, 7, 3, 8, 4, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 2, 9, 7, 8, 4, 3, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 1, 7, 5, 4, 8, 3, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 9, 3, 5, 8, 2, 4, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 5, 2, 7, 3, 8, 4, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 9, 3, 2, 8, 4, 5, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 3, 2, 5, 7, 8, 4, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 3, 2, 8, 7, 4, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 9, 3, 2, 7, 4, 8, 5, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 8, 9, 6, 5, 3, 4, 1, 2 ],
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 9, 5, 7, 6, 3, 4, 1, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 8, 6, 7, 2, 4, 5, 1, 9 ],
[ 2, 3, 9, 5, 4, 6, 7, 8, 1 ],
[ 8, 4, 9, 6, 7, 2, 5, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 8, 4, 7, 6, 2, 5, 1, 9 ],
[ 2, 3, 9, 5, 4, 6, 7, 8, 1 ],
[ 8, 6, 9, 2, 7, 4, 5, 1, 3 ]
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
