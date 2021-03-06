s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[14,6,2]-72-63-2211111-g0";
s`BelyiDBFilename := "9T34-[14,6,2]-72-63-2211111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 14, 6, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 9, 1, 8, 3, 4, 5, 6, 7, 2 ],
[ 8, 2, 9, 4, 5, 6, 7, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 9, 4, 2, 3, 1, 5, 6, 7, 8 ],
[ 8, 5, 3, 4, 2, 6, 7, 1, 9 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 9, 1, 5, 3, 4, 2, 6, 7, 8 ],
[ 8, 2, 6, 4, 5, 3, 7, 1, 9 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
\[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 9, 1, 2, 6, 4, 5, 3, 7, 8 ],
[ 8, 2, 3, 7, 5, 6, 4, 1, 9 ]
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
[ 8, 3, 6, 5, 4, 7, 1, 9, 2 ],
[ 9, 7, 5, 2, 4, 3, 6, 1, 8 ],
[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 3, 2, 6, 4, 7, 8, 9, 1 ],
[ 3, 9, 5, 2, 1, 4, 6, 7, 8 ],
[ 2, 1, 4, 3, 5, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 4, 6, 1, 3, 7, 2, 9, 8 ],
[ 8, 5, 7, 2, 1, 3, 6, 9, 4 ],
[ 9, 3, 2, 4, 5, 6, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 7, 4, 5, 2, 9, 8, 1, 6 ],
[ 6, 1, 5, 3, 4, 9, 2, 7, 8 ],
[ 9, 3, 2, 4, 5, 6, 7, 8, 1 ]
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
