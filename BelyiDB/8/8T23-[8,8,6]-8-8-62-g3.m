s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T23-[8,8,6]-8-8-62-g3";
s`BelyiDBFilename := "8T23-[8,8,6]-8-8-62-g3.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 3, 1, 6, 8, 7, 5, 2 ],
[ 5, 3, 8, 2, 1, 7, 4, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 3, 1, 6, 8, 7, 5, 2 ],
\[ 5, 3, 8, 2, 1, 7, 4, 6 ]:
 Order := 48 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 3, 1, 6, 8, 7, 5, 2 ],
\[ 5, 3, 8, 2, 1, 7, 4, 6 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 3, 1, 6, 8, 7, 5, 2 ],
\[ 5, 3, 8, 2, 1, 7, 4, 6 ]:
 Order := 48 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 8, 5, 7, 6, 4, 1, 3 ],
[ 2, 7, 1, 8, 6, 3, 5, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 3, 1, 6, 8, 7, 5, 2 ],
\[ 5, 3, 8, 2, 1, 7, 4, 6 ]:
 Order := 48 > |
[ 6, 7, 8, 1, 2, 3, 4, 5 ],
[ 6, 4, 1, 3, 2, 8, 5, 7 ],
[ 2, 7, 1, 8, 6, 3, 5, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 3, 1, 6, 8, 7, 5, 2 ],
[ 5, 3, 8, 2, 1, 7, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 7, 4, 6, 5, 3, 8, 2, 1 ],
[ 4, 5, 6, 7, 8, 1, 2, 3 ],
[ 5, 4, 2, 7, 1, 8, 6, 3 ]
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
