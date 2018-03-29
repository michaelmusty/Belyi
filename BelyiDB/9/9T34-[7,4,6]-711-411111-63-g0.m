s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[7,4,6]-711-411111-63-g0";
s`BelyiDBFilename := "9T34-[7,4,6]-711-411111-63-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 7, 2, 3, 4, 5, 6, 8, 9, 1 ],
[ 2, 3, 4, 5, 6, 1, 9, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 9, 2, 8, 4, 5, 6, 7, 1, 3 ],
[ 2, 9, 4, 5, 6, 7, 8, 3, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]:
 Order := 362880 > |
[ 7, 1, 2, 3, 4, 5, 6, 8, 9 ],
[ 4, 2, 3, 9, 5, 6, 7, 1, 8 ],
[ 2, 3, 1, 5, 6, 7, 8, 9, 4 ]
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
[ 9, 2, 3, 1, 4, 5, 6, 7, 8 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 3, 1, 2, 5, 6, 7, 8, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 2, 9, 4, 3, 5, 6, 7, 1 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 9, 1, 5, 3, 6, 7, 8, 4, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 3, 2, 4, 5, 1, 7, 9 ],
[ 2, 3, 9, 4, 5, 6, 7, 8, 1 ],
[ 7, 4, 2, 5, 6, 9, 8, 1, 3 ]
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
