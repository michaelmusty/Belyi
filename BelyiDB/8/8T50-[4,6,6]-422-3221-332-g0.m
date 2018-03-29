s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[4,6,6]-422-3221-332-g0";
s`BelyiDBFilename := "8T50-[4,6,6]-422-3221-332-g0.m";
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
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 8, 3, 7, 4, 1, 5, 2 ],
[ 5, 6, 8, 3, 1, 7, 2, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 8, 3, 7, 4, 1, 5, 2 ],
[ 5, 6, 8, 3, 1, 7, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 5, 6, 3, 4, 7, 1 ],
[ 6, 8, 1, 5, 4, 3, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 1, 4, 5, 8, 3, 7, 6, 2 ],
[ 2, 1, 8, 5, 7, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 6, 8, 3, 7, 4, 1, 5, 2 ],
\[ 5, 6, 8, 3, 1, 7, 2, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 2, 8, 5, 4, 7, 1, 3 ],
[ 5, 7, 2, 8, 1, 4, 3, 6 ]
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
[ 6, 8, 3, 7, 4, 1, 5, 2 ],
[ 5, 6, 8, 3, 1, 7, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 5, 6, 3, 4, 7, 1 ],
[ 6, 8, 1, 5, 4, 3, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 1, 4, 5, 8, 3, 7, 6, 2 ],
[ 2, 1, 8, 5, 7, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 2, 8, 5, 4, 7, 1, 3 ],
[ 5, 7, 2, 8, 1, 4, 3, 6 ]
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
