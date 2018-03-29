s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[7,4,6]-71-41111-332-g0";
s`BelyiDBFilename := "8T50-[7,4,6]-71-41111-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 8, 3, 2, 4, 5, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 3, 2, 5, 6, 4, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 8, 3, 2, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 3, 2, 5, 6, 4, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 8, 3, 2, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 3, 2, 5, 6, 4, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 6, 8, 3, 2, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 3, 2, 5, 6, 4, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 2, 7, 4, 5, 3, 8, 6 ],
[ 3, 1, 2, 6, 4, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 6, 8, 3, 2, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 3, 2, 5, 6, 4, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 7, 3, 8, 5, 6, 4, 2 ],
[ 2, 1, 8, 3, 7, 5, 6, 4 ]
],
[ PermutationGroup<8 |  
\[ 6, 8, 3, 2, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 3, 2, 5, 6, 4, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 5, 2, 8, 4, 3, 6, 7, 1 ],
[ 7, 8, 2, 5, 4, 1, 6, 3 ]
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
[ 6, 8, 3, 2, 4, 5, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 3, 2, 5, 6, 4, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 7, 8, 4, 3, 1, 6, 2 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 6, 8, 5, 3, 4, 7, 1, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 7, 4, 3, 2, 6, 1 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 8, 6, 5, 3, 4, 7, 2, 1 ]
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
