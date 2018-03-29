s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,6,4]-611-62-41111-g0";
s`BelyiDBFilename := "8T50-[6,6,4]-611-62-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 2, 3, 6, 4, 7, 8, 1 ],
[ 5, 8, 2, 3, 1, 4, 6, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 2, 3, 6, 4, 7, 8, 1 ],
\[ 5, 8, 2, 3, 1, 4, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 2, 3, 6, 4, 7, 8, 1 ],
\[ 5, 8, 2, 3, 1, 4, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 2, 3, 6, 4, 7, 8, 1 ],
\[ 5, 8, 2, 3, 1, 4, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 7, 8, 3, 4, 5, 2, 1 ],
[ 1, 8, 7, 4, 5, 6, 2, 3 ]
],
[ PermutationGroup<8 |  
\[ 5, 2, 3, 6, 4, 7, 8, 1 ],
\[ 5, 8, 2, 3, 1, 4, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 3, 2, 7, 4, 5, 8, 1 ],
[ 1, 8, 3, 2, 5, 6, 4, 7 ]
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
[ 5, 2, 3, 6, 4, 7, 8, 1 ],
[ 5, 8, 2, 3, 1, 4, 6, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 2, 4, 5, 6, 7, 1, 8 ],
[ 8, 7, 2, 3, 4, 5, 6, 1 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
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
