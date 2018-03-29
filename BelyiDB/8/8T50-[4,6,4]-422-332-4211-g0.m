s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[4,6,4]-422-332-4211-g0";
s`BelyiDBFilename := "8T50-[4,6,4]-422-332-4211-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 4, 3, 6, 7, 5, 1 ],
[ 3, 8, 1, 4, 5, 7, 2, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 > |
[ 4, 1, 2, 3, 6, 5, 8, 7 ],
[ 4, 8, 2, 1, 6, 7, 5, 3 ],
[ 3, 8, 1, 4, 5, 7, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 > |
[ 4, 1, 2, 3, 6, 5, 8, 7 ],
[ 2, 3, 1, 6, 8, 7, 4, 5 ],
[ 1, 2, 7, 3, 4, 8, 5, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 > |
[ 4, 1, 2, 3, 6, 5, 8, 7 ],
[ 5, 3, 6, 8, 1, 2, 4, 7 ],
[ 6, 2, 7, 5, 3, 1, 4, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 3, 8, 1, 4, 5, 7, 2, 6 ]:
 Order := 40320 > |
[ 4, 1, 2, 3, 6, 5, 8, 7 ],
[ 2, 5, 6, 8, 1, 3, 4, 7 ],
[ 1, 6, 7, 5, 3, 2, 4, 8 ]
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
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 4, 3, 6, 7, 5, 1 ],
[ 3, 8, 1, 4, 5, 7, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 1, 2, 5, 7, 8, 4, 6 ],
[ 7, 2, 3, 1, 8, 4, 6, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 8, 2, 5, 6, 4, 1, 3 ],
[ 6, 7, 3, 8, 5, 4, 2, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 5, 8, 3, 6, 2, 1, 4 ],
[ 8, 7, 6, 4, 5, 2, 3, 1 ]
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
