s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[4,4,12]-41111-44-431-g0";
s`BelyiDBFilename := "8T50-[4,4,12]-41111-44-431-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 12 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 1, 4, 5, 6, 3, 8, 2 ],
[ 3, 2, 8, 6, 4, 5, 1, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 1, 4, 5, 6, 3, 8, 2 ],
\[ 3, 2, 8, 6, 4, 5, 1, 7 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 1, 4, 5, 6, 3, 8, 2 ],
\[ 3, 2, 8, 6, 4, 5, 1, 7 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 1, 4, 5, 6, 3, 8, 2 ],
\[ 3, 2, 8, 6, 4, 5, 1, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 1, 4, 5, 6, 3, 8, 2 ],
[ 3, 2, 8, 6, 4, 5, 1, 7 ]
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
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 1, 4, 5, 6, 3, 8, 2 ],
[ 3, 2, 8, 6, 4, 5, 1, 7 ]
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
