s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[15,20,4]-531-54-411111-g0";
s`BelyiDBFilename := "9T34-[15,20,4]-531-54-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 15, 20, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 4, 1, 2, 3, 9, 5, 6, 7, 8 ],
[ 6, 2, 3, 4, 1, 9, 7, 8, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 4, 1, 2, 3, 7, 8, 6, 9, 5 ],
[ 9, 2, 3, 4, 1, 6, 7, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
\[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
\[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 1, 2, 3, 8, 5, 6, 7, 4 ],
[ 6, 2, 3, 4, 9, 5, 7, 8, 1 ]
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
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 1, 2, 8, 4, 5, 6, 7, 3 ],
[ 6, 2, 3, 9, 5, 4, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 4, 1, 2, 3, 9, 5, 6, 7, 8 ],
[ 6, 2, 3, 4, 1, 9, 7, 8, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 4, 1, 2, 3, 7, 8, 6, 9, 5 ],
[ 9, 2, 3, 4, 1, 6, 7, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 6, 9 ],
[ 9, 1, 2, 3, 8, 5, 6, 7, 4 ],
[ 6, 2, 3, 4, 9, 5, 7, 8, 1 ]
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
