s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,2,15]-611-22211-53-g0";
s`BelyiDBFilename := "8T50-[6,2,15]-611-22211-53-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 2, 15 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 1, 7, 3, 5, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 3, 4, 8, 6, 7, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 4, 8, 7, 1, 5, 6, 3, 2 ],
[ 8, 7, 1, 5, 6, 4, 3, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 3, 8, 1, 4, 7, 6, 5, 2 ],
[ 8, 1, 4, 7, 6, 3, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 3, 8, 1, 7, 5, 6, 4, 2 ],
[ 8, 1, 7, 5, 6, 3, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 2, 1, 7, 3, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 3, 4, 8, 6, 7, 5, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 3, 7, 1, 4, 5, 8, 2, 6 ],
[ 7, 1, 4, 5, 8, 3, 2, 6 ]
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
[ 4, 2, 1, 7, 3, 5, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 3, 4, 8, 6, 7, 5, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 5, 1, 4, 3, 2, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 6, 4, 5, 3, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 8, 3, 2, 5, 1, 6, 7 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 5, 3, 4, 2, 6, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 2, 4, 6, 3, 1, 5, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 6, 3, 4, 2, 7, 5, 8, 1 ]
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
