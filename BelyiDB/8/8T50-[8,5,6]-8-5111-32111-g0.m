s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,5,6]-8-5111-32111-g0";
s`BelyiDBFilename := "8T50-[8,5,6]-8-5111-32111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 5, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 8, 2, 3, 4, 5, 6, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 2, 3, 4, 6, 7, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 2, 1, 3, 4, 5, 7, 8 ],
[ 8, 3, 2, 4, 5, 6, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 1, 3, 2, 4, 5, 7, 8 ],
[ 8, 2, 4, 3, 5, 6, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 7, 2, 3, 1, 4, 5, 6, 8 ],
[ 8, 4, 2, 3, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 8, 2, 3, 4, 5, 6, 1 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 8, 2, 3, 4, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 7, 1, 3, 4, 2, 5, 6, 8 ],
[ 8, 2, 5, 3, 4, 6, 7, 1 ]
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
[ 7, 8, 2, 3, 4, 5, 6, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 2, 3, 4, 6, 7, 5, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 1, 8, 3, 4, 5, 6, 2 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 1, 8, 3, 4, 6, 7, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 7, 3, 4, 2, 6, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 6, 3, 4, 5, 7, 2, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 1, 2, 8, 4, 5, 6, 3 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 1, 2, 8, 4, 6, 7, 5, 3 ]
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
