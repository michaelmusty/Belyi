s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T31-[6,4,6]-63-42111-3222-g0";
s`BelyiDBFilename := "9T31-[6,4,6]-63-42111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 > |
[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
\[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 1296 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
\[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 1296 >) |
[ PermutationGroup<9 |  
\[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
\[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 1296 > |
[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 > |
[ 7, 8, 1, 9, 2, 3, 4, 5, 6 ],
[ 4, 3, 9, 1, 2, 6, 7, 8, 5 ],
[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]
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
