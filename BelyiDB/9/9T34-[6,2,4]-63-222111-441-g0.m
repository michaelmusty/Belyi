s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,2,4]-63-222111-441-g0";
s`BelyiDBFilename := "9T34-[6,2,4]-63-222111-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
\[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
\[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
\[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 9, 7, 8 ],
[ 5, 2, 3, 4, 1, 8, 9, 6, 7 ],
[ 2, 3, 4, 1, 8, 5, 6, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
\[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 9, 7, 8 ],
[ 7, 2, 8, 5, 4, 6, 1, 3, 9 ],
[ 2, 8, 5, 4, 6, 7, 3, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
\[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 9, 7, 8 ],
[ 7, 2, 4, 3, 9, 6, 1, 8, 5 ],
[ 2, 4, 3, 9, 6, 7, 8, 5, 1 ]
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
[ 2, 6, 1, 3, 4, 5, 9, 7, 8 ],
[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ],
[ 2, 9, 4, 5, 6, 3, 7, 1, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 1, 8, 2, 7, 3, 4, 6, 5 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 1, 3, 5, 7, 9, 8, 6, 4, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 1, 8, 9, 7, 3, 4, 6, 2 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ],
[ 1, 9, 5, 7, 2, 8, 6, 4, 3 ]
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
