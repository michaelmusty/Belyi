s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,15,6]-63-531-321111-g0";
s`BelyiDBFilename := "9T34-[6,15,6]-63-531-321111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 15, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 16;
s`BelyiDBPointedSize := 16;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 9, 4, 5, 3, 8, 1 ],
[ 1, 9, 3, 7, 5, 6, 4, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 8, 4, 5, 3, 1, 9 ],
[ 1, 8, 3, 7, 5, 6, 9, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 4, 2, 3, 8, 5, 7, 9, 1 ],
[ 1, 9, 3, 4, 2, 6, 8, 7, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 9, 5, 3, 4, 2, 7, 1, 8 ],
[ 1, 8, 6, 4, 5, 3, 2, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 9, 2, 6, 4, 5, 7, 1, 8 ],
[ 4, 8, 3, 1, 5, 6, 2, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 2, 7, 6, 4, 5, 9, 1, 8 ],
[ 4, 8, 2, 1, 5, 6, 7, 3, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 2, 7, 3, 6, 4, 5, 9, 1, 8 ],
[ 4, 8, 1, 3, 5, 6, 7, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 2, 7, 5, 3, 4, 6, 9, 1, 8 ],
[ 6, 8, 1, 4, 5, 3, 7, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 5, 4, 2, 3, 7, 6, 9, 1, 8 ],
[ 6, 8, 3, 4, 2, 1, 7, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 5, 2, 4, 3, 7, 9, 1, 8 ],
[ 1, 8, 3, 5, 4, 2, 7, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 3, 5, 8, 9, 1, 4 ],
[ 1, 8, 3, 4, 9, 5, 7, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 8, 2, 4, 7, 5, 9, 3, 1 ],
[ 1, 9, 3, 8, 4, 6, 7, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 7, 2, 3, 4, 6, 5, 1, 8 ],
[ 6, 8, 3, 4, 5, 7, 1, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 7, 2, 3, 4, 9, 5, 6, 8 ],
[ 8, 1, 3, 4, 5, 7, 6, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
\[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
\[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 9, 2, 1, 5, 4, 3, 7, 8 ],
[ 1, 4, 3, 7, 6, 5, 2, 8, 9 ]
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
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 1, 3, 4, 5, 8, 2, 9 ],
[ 1, 3, 8, 4, 5, 6, 9, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 9, 4, 5, 3, 8, 1 ],
[ 1, 9, 3, 7, 5, 6, 4, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 8, 4, 5, 3, 1, 9 ],
[ 1, 8, 3, 7, 5, 6, 9, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 4, 2, 3, 8, 5, 7, 9, 1 ],
[ 1, 9, 3, 4, 2, 6, 8, 7, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 9, 5, 3, 4, 2, 7, 1, 8 ],
[ 1, 8, 6, 4, 5, 3, 2, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 9, 2, 6, 4, 5, 7, 1, 8 ],
[ 4, 8, 3, 1, 5, 6, 2, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 2, 7, 6, 4, 5, 9, 1, 8 ],
[ 4, 8, 2, 1, 5, 6, 7, 3, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 2, 7, 3, 6, 4, 5, 9, 1, 8 ],
[ 4, 8, 1, 3, 5, 6, 7, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 2, 7, 5, 3, 4, 6, 9, 1, 8 ],
[ 6, 8, 1, 4, 5, 3, 7, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 5, 4, 2, 3, 7, 6, 9, 1, 8 ],
[ 6, 8, 3, 4, 2, 1, 7, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 5, 2, 4, 3, 7, 9, 1, 8 ],
[ 1, 8, 3, 5, 4, 2, 7, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 7, 2, 3, 5, 8, 9, 1, 4 ],
[ 1, 8, 3, 4, 9, 5, 7, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 8, 2, 4, 7, 5, 9, 3, 1 ],
[ 1, 9, 3, 8, 4, 6, 7, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 7, 2, 3, 4, 6, 5, 1, 8 ],
[ 6, 8, 3, 4, 5, 7, 1, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 7, 2, 3, 4, 9, 5, 6, 8 ],
[ 8, 1, 3, 4, 5, 7, 6, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 9, 2, 1, 5, 4, 3, 7, 8 ],
[ 1, 4, 3, 7, 6, 5, 2, 8, 9 ]
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
