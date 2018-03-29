s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,12,2]-611-431-2222-g0";
s`BelyiDBFilename := "8T50-[6,12,2]-611-431-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 12, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 2, 8, 6, 4, 3, 7, 5, 1 ],
[ 3, 8, 1, 5, 4, 7, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 2, 8, 6, 4, 3, 7, 5, 1 ],
\[ 3, 8, 1, 5, 4, 7, 6, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 2, 8, 6, 4, 3, 7, 5, 1 ],
\[ 3, 8, 1, 5, 4, 7, 6, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 2, 8, 6, 4, 3, 7, 5, 1 ],
\[ 3, 8, 1, 5, 4, 7, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 2, 8, 6, 4, 3, 7, 5, 1 ],
[ 3, 8, 1, 5, 4, 7, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 2, 8, 6, 4, 3, 7, 5, 1 ],
\[ 3, 8, 1, 5, 4, 7, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 4, 8, 3, 2, 6, 7, 5, 1 ],
[ 5, 8, 4, 3, 1, 7, 6, 2 ]
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
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 2, 8, 6, 4, 3, 7, 5, 1 ],
[ 3, 8, 1, 5, 4, 7, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 8, 2, 1, 5, 7, 3, 4, 6 ],
[ 8, 3, 2, 6, 7, 4, 5, 1 ]
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
