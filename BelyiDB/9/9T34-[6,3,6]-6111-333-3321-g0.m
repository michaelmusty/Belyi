s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,3,6]-6111-333-3321-g0";
s`BelyiDBFilename := "9T34-[6,3,6]-6111-333-3321-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 3, 7, 2, 6, 8, 5, 9 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 1, 4, 2, 3, 7, 5, 6, 9, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 1, 3, 7, 2, 6, 8, 5, 9 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 1, 4, 2, 3, 7, 5, 6, 9, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 1, 3, 7, 2, 6, 8, 5, 9 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 1, 4, 2, 3, 7, 5, 6, 9, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 4, 1, 3, 7, 2, 6, 8, 5, 9 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 1, 4, 2, 3, 7, 5, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 5, 4, 9, 7, 8, 2, 1, 3 ],
[ 1, 8, 7, 9, 3, 2, 5, 6, 4 ]
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
[ 4, 1, 3, 7, 2, 6, 8, 5, 9 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 1, 4, 2, 3, 7, 5, 6, 9, 8 ]
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
