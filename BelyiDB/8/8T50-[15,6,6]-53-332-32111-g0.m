s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,6,6]-53-332-32111-g0";
s`BelyiDBFilename := "8T50-[15,6,6]-53-332-32111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 1, 4, 5, 2, 7, 8, 6 ],
[ 7, 1, 5, 3, 4, 8, 2, 6 ],
[ 7, 3, 2, 4, 5, 6, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 1, 2, 5, 6, 4, 8, 7 ],
[ 4, 2, 3, 1, 6, 7, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 8, 1, 4, 3, 7, 5, 6, 2 ],
[ 6, 2, 8, 4, 3, 1, 7, 5 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 6, 4, 2, 3, 7, 8, 5, 1 ],
[ 7, 8, 3, 4, 2, 6, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 8, 1, 7, 5, 4, 3, 6, 2 ],
[ 4, 2, 8, 6, 5, 1, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 5, 2, 7, 8, 6 ],
\[ 7, 1, 5, 3, 4, 8, 2, 6 ],
\[ 7, 3, 2, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 1, 2, 8, 6, 5, 4, 7 ],
[ 6, 2, 3, 1, 7, 4, 5, 8 ]
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
[ 3, 1, 4, 5, 2, 7, 8, 6 ],
[ 7, 1, 5, 3, 4, 8, 2, 6 ],
[ 7, 3, 2, 4, 5, 6, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 5, 2, 6, 7, 8, 1, 4 ],
[ 6, 7, 8, 1, 2, 4, 5, 3 ],
[ 2, 8, 4, 3, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 5, 4, 6, 7, 1, 2, 3 ],
[ 8, 6, 7, 2, 3, 4, 5, 1 ],
[ 2, 3, 1, 5, 4, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 5, 2, 8, 7, 4, 1, 6 ],
[ 4, 7, 6, 1, 2, 8, 5, 3 ],
[ 2, 8, 4, 3, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 5, 2, 8, 1, 4, 3, 6 ],
[ 4, 5, 6, 7, 2, 8, 1, 3 ],
[ 2, 8, 4, 3, 5, 6, 7, 1 ]
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
