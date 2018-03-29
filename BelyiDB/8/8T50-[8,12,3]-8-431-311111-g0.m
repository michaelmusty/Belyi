s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,12,3]-8-431-311111-g0";
s`BelyiDBFilename := "8T50-[8,12,3]-8-431-311111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 12, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 7, 4, 5, 6, 2, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 7, 4, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 7, 4, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 7, 4, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 1, 2, 3, 7, 5, 6, 8 ],
[ 8, 2, 3, 4, 1, 6, 7, 5 ]
],
[ PermutationGroup<8 |  
\[ 3, 7, 4, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 4, 2, 3, 8, 5, 6, 7 ],
[ 5, 1, 3, 4, 2, 6, 7, 8 ]
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
[ 3, 7, 4, 5, 6, 2, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 5, 8, 2, 6, 7, 1, 4 ],
[ 1, 7, 4, 8, 2, 5, 6, 3 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
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
