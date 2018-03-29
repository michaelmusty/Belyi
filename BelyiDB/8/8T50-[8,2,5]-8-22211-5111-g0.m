s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,2,5]-8-22211-5111-g0";
s`BelyiDBFilename := "8T50-[8,2,5]-8-22211-5111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 2, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 1, 8, 7, 6, 4, 3, 2 ],
[ 1, 2, 8, 7, 6, 5, 4, 3 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 1, 8, 7, 6, 4, 3, 2 ],
\[ 1, 2, 8, 7, 6, 5, 4, 3 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 1, 8, 7, 6, 4, 3, 2 ],
\[ 1, 2, 8, 7, 6, 5, 4, 3 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 1, 8, 7, 6, 4, 3, 2 ],
\[ 1, 2, 8, 7, 6, 5, 4, 3 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 3, 2, 5, 4, 6, 7, 1, 8 ]
],
[ PermutationGroup<8 |  
\[ 5, 1, 8, 7, 6, 4, 3, 2 ],
\[ 1, 2, 8, 7, 6, 5, 4, 3 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 8, 2, 4, 3, 6, 5, 7, 1 ],
[ 2, 4, 3, 6, 5, 7, 1, 8 ]
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
[ 5, 1, 8, 7, 6, 4, 3, 2 ],
[ 1, 2, 8, 7, 6, 5, 4, 3 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 7, 3, 6, 4, 2, 1 ],
[ 1, 8, 7, 4, 6, 5, 3, 2 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
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
