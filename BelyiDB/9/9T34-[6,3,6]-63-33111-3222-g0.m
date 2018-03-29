s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,3,6]-63-33111-3222-g0";
s`BelyiDBFilename := "9T34-[6,3,6]-63-33111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 5, 8, 1, 4, 3, 6, 7, 9, 2 ],
[ 6, 3, 9, 5, 4, 1, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 2, 1, 7, 5, 4, 6, 8, 3 ],
[ 7, 3, 2, 9, 6, 5, 1, 4, 8 ]
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
[ 2, 6, 1, 5, 3, 4, 8, 9, 7 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 2, 9, 5, 6, 3, 4, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 7, 6, 8, 2, 5, 1, 9, 4 ],
[ 2, 9, 4, 5, 3, 6, 7, 8, 1 ],
[ 7, 4, 9, 2, 6, 5, 1, 3, 8 ]
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
