s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[7,6,6]-711-6111-6111-g0";
s`BelyiDBFilename := "9T34-[7,6,6]-711-6111-6111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 5, 4, 6, 7, 9 ],
[ 2, 3, 4, 5, 9, 6, 7, 8, 1 ],
[ 1, 2, 3, 6, 4, 7, 8, 9, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 1, 2, 3, 5, 4, 6, 7, 9 ],
\[ 2, 3, 4, 5, 9, 6, 7, 8, 1 ],
\[ 1, 2, 3, 6, 4, 7, 8, 9, 5 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 1, 2, 3, 5, 4, 6, 7, 9 ],
\[ 2, 3, 4, 5, 9, 6, 7, 8, 1 ],
\[ 1, 2, 3, 6, 4, 7, 8, 9, 5 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 8, 1, 2, 3, 5, 4, 6, 7, 9 ],
\[ 2, 3, 4, 5, 9, 6, 7, 8, 1 ],
\[ 1, 2, 3, 6, 4, 7, 8, 9, 5 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 1, 2, 3, 9, 4, 5, 6, 7, 8 ],
[ 8, 1, 2, 3, 5, 6, 7, 9, 4 ]
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
[ 8, 1, 2, 3, 5, 4, 6, 7, 9 ],
[ 2, 3, 4, 5, 9, 6, 7, 8, 1 ],
[ 1, 2, 3, 6, 4, 7, 8, 9, 5 ]
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
