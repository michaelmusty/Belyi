s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,5,6]-81-51111-6111-g0";
s`BelyiDBFilename := "9T34-[8,5,6]-81-51111-6111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 5, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 2, 7, 3, 4, 5, 8, 9, 1 ],
[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 2, 7, 3, 4, 5, 8, 9, 1 ],
\[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 2, 7, 3, 4, 5, 8, 9, 1 ],
\[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 2, 7, 3, 4, 5, 8, 9, 1 ],
\[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 3, 4, 9, 5, 6, 7, 8, 1 ],
[ 1, 2, 3, 5, 6, 7, 8, 9, 4 ]
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
[ 6, 2, 7, 3, 4, 5, 8, 9, 1 ],
[ 1, 9, 2, 4, 5, 6, 3, 7, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
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
