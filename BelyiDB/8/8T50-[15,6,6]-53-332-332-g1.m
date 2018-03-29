s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,6,6]-53-332-332-g1";
s`BelyiDBFilename := "8T50-[15,6,6]-53-332-332-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 8, 6, 2, 3, 1, 5, 4 ],
[ 2, 8, 4, 5, 3, 7, 6, 1 ],
[ 7, 3, 4, 2, 6, 5, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 8, 6, 2, 3, 1, 5, 4 ],
\[ 2, 8, 4, 5, 3, 7, 6, 1 ],
\[ 7, 3, 4, 2, 6, 5, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 8, 6, 2, 3, 1, 5, 4 ],
\[ 2, 8, 4, 5, 3, 7, 6, 1 ],
\[ 7, 3, 4, 2, 6, 5, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 7, 8, 6, 2, 3, 1, 5, 4 ],
\[ 2, 8, 4, 5, 3, 7, 6, 1 ],
\[ 7, 3, 4, 2, 6, 5, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 1, 5, 6, 4, 8, 2 ],
[ 4, 3, 8, 1, 6, 7, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 7, 8, 6, 2, 3, 1, 5, 4 ],
\[ 2, 8, 4, 5, 3, 7, 6, 1 ],
\[ 7, 3, 4, 2, 6, 5, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 4, 8, 6, 7, 2, 5, 1 ],
[ 7, 8, 6, 1, 2, 3, 4, 5 ]
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
[ 7, 8, 6, 2, 3, 1, 5, 4 ],
[ 2, 8, 4, 5, 3, 7, 6, 1 ],
[ 7, 3, 4, 2, 6, 5, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 7, 8, 1, 2, 3, 4, 6 ],
[ 2, 8, 4, 5, 3, 7, 6, 1 ],
[ 3, 4, 7, 6, 8, 2, 1, 5 ]
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
