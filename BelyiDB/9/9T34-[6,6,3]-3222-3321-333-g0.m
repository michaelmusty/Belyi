s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,3]-3222-3321-333-g0";
s`BelyiDBFilename := "9T34-[6,6,3]-3222-3321-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 1, 2, 8, 7, 9, 5, 4, 6 ],
[ 6, 2, 7, 1, 8, 4, 9, 5, 3 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 1, 2, 8, 7, 9, 5, 4, 6 ],
\[ 6, 2, 7, 1, 8, 4, 9, 5, 3 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 1, 2, 8, 7, 9, 5, 4, 6 ],
\[ 6, 2, 7, 1, 8, 4, 9, 5, 3 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 1, 2, 8, 7, 9, 5, 4, 6 ],
\[ 6, 2, 7, 1, 8, 4, 9, 5, 3 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
[ 1, 5, 9, 3, 6, 2, 8, 7, 4 ],
[ 4, 1, 6, 2, 9, 8, 5, 3, 7 ]
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
[ 3, 1, 2, 8, 7, 9, 5, 4, 6 ],
[ 6, 2, 7, 1, 8, 4, 9, 5, 3 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
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
