s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,3,4]-8-3311-41111-g0";
s`BelyiDBFilename := "8T50-[8,3,4]-8-3311-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 2, 1, 4, 5, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 6, 2, 3, 4, 5, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 8, 2, 1, 4, 5, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 2, 3, 4, 5, 7, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 2, 1, 4, 5, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 2, 3, 4, 5, 7, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 2, 1, 4, 5, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 2, 3, 4, 5, 7, 8, 1 ]:
 Order := 40320 > |
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 1, 2, 4, 5, 3, 7, 8, 6 ],
[ 2, 5, 3, 4, 8, 6, 7, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 2, 1, 4, 5, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 6, 2, 3, 4, 5, 7, 8, 1 ]
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
