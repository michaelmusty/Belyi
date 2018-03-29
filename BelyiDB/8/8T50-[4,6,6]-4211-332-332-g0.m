s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[4,6,6]-4211-332-332-g0";
s`BelyiDBFilename := "8T50-[4,6,6]-4211-332-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 2, 8, 6, 5, 4, 7, 3, 1 ],
[ 5, 8, 1, 7, 3, 4, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 2, 8, 6, 5, 4, 7, 3, 1 ],
[ 5, 8, 1, 7, 3, 4, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 2, 8, 5, 7, 3, 4, 6, 1 ],
[ 6, 8, 1, 5, 7, 3, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 3, 6, 5, 7, 1, 8, 4, 2 ],
[ 7, 5, 8, 1, 2, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8 ],
\[ 2, 8, 6, 5, 4, 7, 3, 1 ],
\[ 5, 8, 1, 7, 3, 4, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 3, 8, 5, 7, 1, 2, 4, 6 ],
[ 7, 5, 6, 1, 8, 3, 4, 2 ]
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
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 2, 8, 6, 5, 4, 7, 3, 1 ],
[ 5, 8, 1, 7, 3, 4, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 2, 8, 5, 7, 3, 4, 6, 1 ],
[ 6, 8, 1, 5, 7, 3, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 3, 6, 5, 7, 1, 8, 4, 2 ],
[ 7, 5, 8, 1, 2, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 7, 8 ],
[ 3, 8, 5, 7, 1, 2, 4, 6 ],
[ 7, 5, 6, 1, 8, 3, 4, 2 ]
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
