s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,4,6]-53-422-32111-g0";
s`BelyiDBFilename := "8T50-[15,4,6]-53-422-32111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 4, 1, 5, 3, 8, 6, 7 ],
[ 6, 3, 2, 5, 4, 7, 8, 1 ],
[ 2, 8, 4, 3, 5, 6, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 2, 1, 5, 3, 6, 4, 8, 7 ],
[ 3, 2, 1, 4, 6, 7, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 5, 3, 2, 1, 6, 4, 8, 7 ],
[ 1, 4, 3, 2, 6, 7, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 1, 5, 4, 8, 6, 2 ],
[ 4, 3, 8, 1, 5, 6, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 6, 1, 4, 3, 7, 8, 5, 2 ],
[ 7, 2, 8, 4, 3, 6, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 4, 1, 5, 3, 8, 6, 7 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ],
\[ 2, 8, 4, 3, 5, 6, 7, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 6, 1, 7, 5, 4, 8, 3, 2 ],
[ 4, 2, 8, 7, 5, 6, 1, 3 ]
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
[ 2, 4, 1, 5, 3, 8, 6, 7 ],
[ 6, 3, 2, 5, 4, 7, 8, 1 ],
[ 2, 8, 4, 3, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 1, 6, 3, 2, 4, 8, 5 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 1, 6, 3, 5, 7, 2, 4, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 1, 5, 2, 6, 3, 8, 4 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 1, 3, 5, 7, 2, 6, 4, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 8, 5, 6, 2, 3, 7 ],
[ 2, 7, 4, 3, 6, 5, 8, 1 ],
[ 1, 5, 2, 8, 3, 6, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 1, 3, 6, 4, 2, 7 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 3, 5, 4, 6, 7, 1 ]
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
